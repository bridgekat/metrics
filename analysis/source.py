"""Checks that read the source files rather than the compiled terms."""
import os
import re

HEADER = "Upstreaming candidate"


def upstream_header_drift(repo, lib="Numlib"):
    """H1. Files that open with the "Upstreaming candidate" header, which asks them to stay "free
    of dependencies on the rest of Numlib other than other upstreaming candidates", and import a
    module of the library that does not carry the header. Returns (file, [offending imports])."""
    marked = {}
    imports = {}
    for base, _, files in os.walk(os.path.join(repo, lib)):
        for f in files:
            if not f.endswith(".lean"):
                continue
            path = os.path.join(base, f)
            mod = os.path.relpath(path, repo)[:-5].replace(os.sep, ".")
            with open(path, encoding="utf-8") as h:
                text = h.read()
            marked[mod] = HEADER in text[:4000]
            imports[mod] = re.findall(r"^(?:public\s+)?import\s+([\w.]+)", text, re.M)
    out = []
    for mod, is_marked in sorted(marked.items()):
        if not is_marked:
            continue
        bad = [i for i in imports[mod] if i.startswith(lib + ".") and not marked.get(i, False)]
        if bad:
            out.append((mod, bad))
    return out, sum(marked.values()), len(marked)


if __name__ == "__main__":
    import sys
    drift, n_marked, n = upstream_header_drift(sys.argv[1])
    print(f"{len(drift)} of {n_marked} marked files (of {n}) import an unmarked module of the library")
    for mod, bad in drift:
        print(f"  {mod}: {', '.join(bad)}")
