import json, sys, os, time
sys.path.insert(0, '/root/LLM-FOR-SCHEDULING/adversary_search')
os.chdir('/root/LLM-FOR-SCHEDULING/adversary_search')
import template_schema
from m4_search import opt

tpl = json.load(open('seeds/rudin2001_m5.json'))
sizes, meta = template_schema.materialize(tpl)
print("jobs:", len(sizes), flush=True)

import math
L = 1
for s in sizes:
    L = math.lcm(L, s.denominator)
jobs = tuple(int(s * L) for s in sizes)
print("int max:", max(jobs), flush=True)

for k in [5, 10, 15, 20, 30, 40, 50, 60, 71]:
    t0 = time.time()
    v = opt(jobs[:k], 5)
    print(f"opt(prefix {k}): {v}  ({time.time()-t0:.2f}s)", flush=True)