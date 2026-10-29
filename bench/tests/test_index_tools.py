"""Exercise the reference-only tools index against planted package/cache sources."""

import importlib.util
import json
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch


class ToolsIndexTests(unittest.TestCase):
    def test_standalone_references_are_indexed_without_package_or_cache_sources(self):
        spec = importlib.util.spec_from_file_location("index_tools", Path(__file__).parents[1] / "index_tools.py")
        module = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(module)
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            tools = root / "tools"
            package = tools / "task018_split_count"
            (package / "src").mkdir(parents=True)
            cache = package / ".sigil/deps/sigil/fmt/hash/src"
            cache.mkdir(parents=True)
            source = "module tool;\npub fn tool_main(p:i64,n:i64)->i64 ! {Alloc} { return 0; }\n"
            (tools / "task001_echo.sigil").write_text(source)
            (tools / "task018_split_count.sigil").write_text(source)
            (package / "src/tool.sigil").write_text(source)
            (cache / "tool.sigil").write_text(source)
            cursor = root / "cursor.jsonl"
            cursor.write_text(json.dumps({"name": "removed.sigil", "categories": ["task"], "first_body_line": "stale", "line_count": 58}) + "\n")
            index = tools / "INDEX.md"
            with patch.multiple(module, TOOLS_DIR=tools, CURSOR=cursor, INDEX_MD=index):
                self.assertEqual(module.process_batch(0, 1000), (2, 2))
                rows = module.load_cursor()
                self.assertEqual(set(rows), {"task001_echo.sigil", "task018_split_count.sigil"})
                self.assertEqual(rows["task018_split_count.sigil"]["categories"], ["alloc", "task"])
                first = index.read_bytes()
                module.process_batch(0, 1000)
                self.assertEqual(index.read_bytes(), first)


if __name__ == "__main__":
    unittest.main()
