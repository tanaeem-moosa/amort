#!/usr/bin/env python3
"""
Unit test asserting that docs/ is self-contained and serves real chapters (§2.1).

Starts a local HTTP server in docs/ and verifies:
1. docs/tree.json is served and matches tutorial/tree.json
2. docs/chapters/binary_gcd.md, euclid_gcd.md, and insertion_sort.md are served
3. For each of Binary GCD, Euclid, and Insertion Sort, the first heading of the
   served chapter equals the corresponding .md file's first heading.
"""

import http.server
import json
import socketserver
import threading
import unittest
import urllib.request
from pathlib import Path


class TestSiteServing(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.repo_root = Path(__file__).resolve().parent.parent
        cls.docs_dir = cls.repo_root / "docs"

        class QuietHandler(http.server.SimpleHTTPRequestHandler):
            def __init__(self, *args, **kwargs):
                super().__init__(*args, directory=str(cls.docs_dir), **kwargs)

            def log_message(self, format, *args):
                pass  # Suppress server logs during test run

        cls.httpd = socketserver.TCPServer(("127.0.0.1", 0), QuietHandler)
        cls.port = cls.httpd.server_address[1]
        cls.server_thread = threading.Thread(target=cls.httpd.serve_forever, daemon=True)
        cls.server_thread.start()

    @classmethod
    def tearDownClass(cls):
        cls.httpd.shutdown()
        cls.httpd.server_close()

    def _fetch(self, path: str) -> str:
        url = f"http://127.0.0.1:{self.port}/{path.lstrip('/')}"
        req = urllib.request.Request(url, headers={"User-Agent": "TestClient"})
        with urllib.request.urlopen(req, timeout=5) as resp:
            self.assertEqual(resp.status, 200)
            return resp.read().decode("utf-8")

    def test_tree_json_served_identically(self):
        served_json = json.loads(self._fetch("tree.json"))
        original_json = json.loads((self.repo_root / "tutorial/tree.json").read_text(encoding="utf-8"))
        self.assertEqual(served_json, original_json)

    def test_tree_data_js_served(self):
        served_js = self._fetch("tree_data.js")
        self.assertIn("window.__TREE_DATA_FALLBACK__ = ", served_js)

    def test_binary_gcd_chapter_heading(self):
        served_content = self._fetch("chapters/binary_gcd.md")
        original_content = (self.repo_root / "tutorial/binary_gcd.md").read_text(encoding="utf-8")

        served_first_heading = served_content.strip().splitlines()[0]
        original_first_heading = original_content.strip().splitlines()[0]

        self.assertEqual(served_first_heading, original_first_heading)
        self.assertTrue(served_first_heading.startswith("# 🌱 Binary GCD"))
        self.assertNotIn("facades or circular shortcuts", served_content)

    def test_euclid_gcd_chapter_heading(self):
        served_content = self._fetch("chapters/euclid_gcd.md")
        original_content = (self.repo_root / "tutorial/euclid_gcd.md").read_text(encoding="utf-8")

        served_first_heading = served_content.strip().splitlines()[0]
        original_first_heading = original_content.strip().splitlines()[0]

        self.assertEqual(served_first_heading, original_first_heading)
        self.assertTrue(served_first_heading.startswith("# 🏛️ Euclid's GCD"))
        self.assertNotIn("facades or circular shortcuts", served_content)

    def test_insertion_sort_chapter_heading(self):
        served_content = self._fetch("chapters/insertion_sort.md")
        original_content = (self.repo_root / "tutorial/insertion_sort.md").read_text(encoding="utf-8")

        served_first_heading = served_content.strip().splitlines()[0]
        original_first_heading = original_content.strip().splitlines()[0]

        self.assertEqual(served_first_heading, original_first_heading)
        self.assertTrue(served_first_heading.startswith("# 🗂️ Insertion Sort"))
        self.assertNotIn("facades or circular shortcuts", served_content)


if __name__ == "__main__":
    unittest.main()
