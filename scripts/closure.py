"""Print sparse-checkout patterns for the import closure of the given Stacks modules."""
import re
import subprocess
import sys

repo, rev, targets = sys.argv[1], sys.argv[2], sys.argv[3:]


def git(*args):
    return subprocess.run(["git", "-C", repo, *args], capture_output=True, text=True,
                          encoding="utf8", check=True).stdout


files = {f[:-5].replace("/", ".") for f in git("ls-tree", "-r", "--name-only", rev).split("\n")
         if f.endswith(".lean")}
imports = {}
pending = None
# -A1 catches imports whose module name is on the next line.
for line in git("grep", "-A1", "-E", r"^(public )?(meta )?import( |$)", rev, "--", "*.lean").split("\n"):
    m = re.match(r"[^:]+:(.+?)\.lean[:-](.*)$", line)
    if not m:
        pending = None
        continue
    mod, text = m.group(1).replace("/", "."), m.group(2).strip()
    if pending == mod and re.fullmatch(r"[\w.]+", text):
        imports.setdefault(mod, set()).add(text)
    pending = None
    i = re.match(r"(?:public )?(?:meta )?import(?: all)?(?: (\S+))?$", text)
    if i:
        if i.group(1):
            imports.setdefault(mod, set()).add(i.group(1))
        else:
            pending = mod

seen, stack = set(), list(targets)
while stack:
    mod = stack.pop()
    if mod in seen:
        continue
    seen.add(mod)
    stack.extend(i for i in imports.get(mod, ()) if i in files)

for pattern in ["/lakefile.toml", "/lake-manifest.json", "/lean-toolchain", "/LICENSE"]:
    print(pattern)
for mod in sorted(seen):
    print("/" + mod.replace(".", "/") + ".lean")
