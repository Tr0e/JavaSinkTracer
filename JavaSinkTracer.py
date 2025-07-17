"""
@File：JavaSinkTracer.py
@Time：2025/02/15 10:39
@Auth：Tr0e
@Github：https://github.com/Tr0e
@Description：基于javalang库，对漏洞Sink点进行回溯，提取Java源代码中“函数级”的污点调用链路
"""
import argparse
import os
import json
import time

import javalang
from javalang import tree
from collections import deque
from typing import Dict, List, Union
from colorama import Fore, init
from javalang.tree import ClassDeclaration

from JavaCodeExtract import extract_method_definition
from AutoVulReport import generate_markdown_report

init(autoreset=True)


class JavaSinkTracer:
    def __init__(self, project_path: str, rules_path: str):
        self.project_path = project_path
        self.rules = self._load_rules(rules_path)
        self.call_graph: Dict[str, List[str]] = {}
        self.class_methods: Dict[str, Dict[str, Union[str, Dict[str, Dict[str, bool]]]]] = {}

    @staticmethod
    def _load_rules(path: str) -> dict:
        """
        读取本地json格式的配置文件的数据
        """
        with open(path, "r", encoding="utf-8") as f:
            rules = json.load(f)
            print(f"[+]成功加载Rules：{rules}")
            return rules

    def _is_excluded(self, file_path):
        """
        判断当前的代码路径是不是配置文件设置的无需扫描的白名单路径
        """
        rel_path = os.path.relpath(file_path, self.project_path)
        return any(p in rel_path.split(os.sep) for p in self.rules["path_exclusions"])

    def build_ast(self):
        """
        构建项目AST并建立调用关系
        """
        print(f"[+]正构建项目AST：{self.project_path}")
        for root, _, files in os.walk(self.project_path):
            for file in files:
                if file.endswith(".java") and not self._is_excluded(root):
                    try:
                        print(f"[+]正在分析的文件：{file}")
                        self._process_file(os.path.join(root, file))
                    except Exception:
                        continue
        print(Fore.LIGHTBLUE_EX + f"[+]AST构建全部完成！")
        # print(f"[+]已构建的调用关系图：{self.call_graph}")
        # print(f"[+]已构建的类方法信息：{self.class_methods}")

    def _process_file(self, file_path: str):
        with open(file_path, "r", encoding="utf-8") as f:
            try:
                code_tree = javalang.parse.parse(f.read())
                print(Fore.GREEN + f"[+]已成功解析文件：{file_path}")
                self._extract_class_info(code_tree, file_path)
                self._build_call_graph(code_tree)
            except javalang.parser.JavaSyntaxError as e:
                print(f"Syntax error in {file_path}: {e}")

    def _extract_class_info(self, code_tree, file_path: str):
        """
        提取Java项目中类和方法信息，包含完整文件路径
        """
        MAPPING_ANNOTATIONS = {
            "GetMapping", "PostMapping", "RequestMapping", "PutMapping", "DeleteMapping",
            "Path", "GET", "POST", "PUT", "DELETE"
        }
        for path, node in code_tree.filter(ClassDeclaration):
            class_name = node.name
            methods_info = {}
            for method_node in node.methods:
                method_name = method_node.name
                requires_params = len(method_node.parameters) > 0
                has_mapping_annotation = False
                if method_node.annotations:
                    for annotation in method_node.annotations:
                        annotation_name = annotation.name.lstrip("@")
                        if annotation_name in MAPPING_ANNOTATIONS:
                            has_mapping_annotation = True
                            break
                methods_info[method_name] = {
                    "requires_params": requires_params,
                    "has_mapping_annotation": has_mapping_annotation
                }
            self.class_methods[class_name] = {
                "file_path": file_path,
                "methods": methods_info
            }

    def _build_call_graph(self, file_code_tree):
        """
        构建所有类中方法的调用图
        """
        variable_symbols = self.get_variable_symbols(file_code_tree)
        for path, node in file_code_tree.filter(javalang.tree.MethodInvocation):
            caller = self._get_current_method_from_path(path)
            callee = "[!]callee解析失败"
            if node.qualifier:
                default = node.qualifier.split('.')[0] if '.' in node.qualifier and node.qualifier.split('.')[0][0].isupper() else node.qualifier
                base_type = variable_symbols.get(node.qualifier, default)
                base_type = base_type.split('<')[0]
                callee = f"{base_type}:{node.member}"
            elif node.qualifier is None:
                base_type = '[!]base_type解析失败'
                if self.is_string_literal_caller(path):
                    base_type = "String"
                else:
                    try:
                        parent_node = path[-2] if len(path) > 1 else None
                        if isinstance(parent_node, javalang.tree.ClassCreator):
                            base_type = parent_node.type.name
                        elif isinstance(parent_node, javalang.tree.ClassReference):
                            base_type = parent_node.type.name
                        else:
                            base_type = self.call_graph[caller][-1].split(':')[0]
                    except Exception as e:
                        print(Fore.RED + f"[!]待排查异常解析：{caller} -> {node.member}, 异常信息：{e}")
                callee = f"{base_type}:{node.member}"
            elif '.' not in node.member:
                callee = f"{caller.split(':')[0]}:{node.member}"
            if str(callee).startswith('[!]'):
                print(Fore.RED + f"[CallGraph] {caller} -> {callee}")
            else:
                print(f"[CallGraph] {caller} -> {callee}")
            self.call_graph.setdefault(caller, []).append(callee)

    @staticmethod
    def is_string_literal_caller(path):
        """
        判断方法调用是否由字符串常量
        """
        for parent in reversed(path):
            if isinstance(parent, javalang.tree.Literal) and isinstance(parent.value, str):
                return True
        return False

    @staticmethod
    def get_variable_symbols(file_code_tree):
        """
        提取类中所有变量声明及其类型
        """
        variable_symbols = {}
        for path, node in file_code_tree:
            if isinstance(node, javalang.tree.LocalVariableDeclaration):
                var_type = node.type.name
                for declarator in node.declarators:
                    variable_symbols[declarator.name] = var_type
            elif isinstance(node, javalang.tree.FieldDeclaration):
                var_type = node.type.name
                for declarator in node.declarators:
                    variable_symbols[declarator.name] = var_type
            elif isinstance(node, javalang.tree.MethodDeclaration):
                for param in node.parameters:
                    var_type = param.type.name
                    variable_symbols[param.name] = var_type
        return variable_symbols

    def _get_current_method_from_path(self, path) -> str:
        """
        通过AST路径直接获取当前函数节点所对应的类的信息，用于构建调用图
        """
        for node in reversed(path):
            if isinstance(node, javalang.tree.MethodDeclaration):
                class_node = self.find_parent_class(path)
                return f"{class_node.name}:{node.name}"
        return "unknown:unknown"

    def find_taint_paths(self) -> List[dict]:
        print("-" * 50)
        print(f"[+]正在审计源项目：{self.project_path}")
        # print(Fore.MAGENTA + f"[+]提取到的类函数字典：{self.class_methods}")
        results = []
        for rule in self.rules["sink_rules"]:
            for sink in rule["sinks"]:
                class_name, methods = sink.split(":")
                for method in methods.split("|"):
                    class_name = class_name.split('.')[-1]
                    sink_point = f"{class_name}:{method}"
                    print(f"[+]正在审计sink点：{sink_point}")
                    paths = self._trace_back(sink_point, self.rules["depth"])
                    if paths:
                        results.append({
                            "vul_type": rule["sink_name"],
                            "sink_desc": rule["sink_desc"],
                            "severity": rule["severity_level"],
                            "sink": sink_point,
                            "call_chains": self.process_call_stacks(self.project_path, paths)
                        })
        print("-" * 50)
        return results

    @staticmethod
    def process_call_stacks(root_dir, call_stacks):
        results = []
        for stack in call_stacks:
            visited = set()
            chain = []
            code_list = []
            queue = []
            for item in stack:
                cls, mtd = item.split(':', 1)
                queue.append((cls, mtd))
            while queue:
                cls, mtd = queue.pop(0)
                key = f"{cls}:{mtd}"
                if key in visited:
                    continue
                visited.add(key)
                path, code = extract_method_definition(root_dir, cls, mtd)
                if not path or not code:
                    continue
                chain.append(f"{path}:{mtd}")
                code_list.append(code)
            results.append({"chain": chain, "code": code_list})
        return results

    def _trace_back(self, sink: str, max_depth: int) -> List[List[str]]:
        """
        根据最大追溯深度的限制，回溯污点传播的路径，支持多级调用链展开
        """
        paths = []
        queue = deque([([sink], 0)])
        while queue:
            current_path, current_depth = queue.popleft()
            if current_depth >= max_depth:
                continue
            current_sink = current_path[0]
            caller_methods = [
                caller
                for caller, callees in self.call_graph.items()
                if current_sink in callees
            ]
            if not caller_methods:
                continue
            else:
                print(Fore.MAGENTA + f"[*]需要追溯调用点: {caller_methods}")
            for caller in caller_methods:
                if not self.is_has_parameters(caller.split(':')[0], caller.split(':')[1]):
                    print(Fore.RED + f"[!]发现无参的函数：{caller}，此链路忽略不计！")
                    continue
                new_path = [caller] + current_path
                print(Fore.YELLOW + f"[→]正在追溯的路径: [{' → '.join(new_path)}]")
                if self.is_entry_point(caller):
                    paths.append(new_path)
                    print(Fore.LIGHTGREEN_EX + f"[✓]发现完整调用链: {new_path}")
                else:
                    queue.append((new_path, current_depth + 1))
        return paths

    def is_has_parameters(self, class_name: str, method_name: str) -> bool:
        """
        判断给定类中的给定方法是否包含参数
        """
        try:
            class_info = self.class_methods.get(class_name, {})
            method_info = class_info.get("methods", {}).get(method_name, {})
            return method_info.get("requires_params", True)
        except KeyError:
            return True

    def is_entry_point(self, method: str) -> bool:
        """
        判断当前追溯到的函数是否已经是程序的外部入口点（MAPPING_ANNOTATIONS相关函数）
        """
        class_name, method_name = method.split(":")
        is_method_entry_point = False
        class_info = self.class_methods.get(class_name, {})
        method_info = class_info.get("methods", {}).get(method_name, {})
        if method_info:
            is_method_entry_point = method_info.get("has_mapping_annotation", False)
        return is_method_entry_point

    @staticmethod
    def find_parent_class(path) -> javalang.tree.ClassDeclaration:
        """
        从AST路径中查找最近的类声明或接口声明
        """
        for node in reversed(path):
            if isinstance(node, (javalang.tree.ClassDeclaration, javalang.tree.InterfaceDeclaration)):
                return node
        raise ValueError("No class declaration found")


def run():
    start_time = time.time()
    print(Fore.LIGHTCYAN_EX + """
      ███████╗███████╗ ██████╗  
     ██╔════╝██╔════╝██╔════╝ 
     ███████╗█████╗  ██║     
     ╚════██║██╔══╝  ██║      
     ███████║███████╗╚██████╗ 
     ╚══════╝╚══════╝ ╚═════╝ 
    """ + Fore.LIGHTGREEN_EX + """
    Java源代码漏洞审计工具_Tr0e
    """ + Fore.RESET)
    parser = argparse.ArgumentParser(description="JavaSinkTracer")
    parser.add_argument('-p', "--projectPath", type=str, default='D:/Code/Github/java-sec-code', help=f"待扫描的项目本地路径根目录，默认值：D:/Code/Github/java-sec-code")
    parser.add_argument('-o', "--outputPath", type=str, default='Result', help=f"指定扫描报告输出的本地路径根目录，默认值：当前项目根路径下的 Result 子文件夹")
    args = parser.parse_args()
    java_project_path = args.projectPath.replace('\\', '/')
    java_project_name = java_project_path.rstrip('/').split('/')[-1]
    print(f'[+]待扫描的project_name: {java_project_name}, project_path: {java_project_path}')
    analyzer = JavaSinkTracer(java_project_path, "Rules/rules.json")
    analyzer.build_ast()
    vulnerabilities = analyzer.find_taint_paths()
    print(Fore.LIGHTGREEN_EX + f"[+]代码审计结果汇总：\n{json.dumps(vulnerabilities, indent=2, ensure_ascii=False)}")
    target_dir = os.path.join("Result", java_project_name)
    os.makedirs(target_dir, exist_ok=True)
    sink_save_file = os.path.join(target_dir, f"sink_chains.json")
    with open(sink_save_file, "w", encoding="utf-8") as file:
        json.dump(vulnerabilities, file, indent=4, ensure_ascii=False)
    generate_markdown_report(java_project_name, java_project_path, sink_save_file, args.outputPath)
    print(f"[+]主进程任务完成，耗时：{round(time.time() - start_time, 2)}秒")


if __name__ == "__main__":
    run()
