#!/usr/bin/env python3
"""Check the registry complement and synchronized documentation; no status upgrades."""
import argparse
import json
import re
from pathlib import Path
ROOT = Path(__file__).resolve().parents[1]
PROMOTIONS = {
 'E15': ('Models/ModalEntropyBounds.lean', 'ModalGrowthBound', 'modalGrowth_nonpositive_above_threshold'),
 'E31': ('Models/ModalEntropyBounds.lean', 'EntropyDissipationBound', 'cumulative_dissipation_le_entropy_drop'),
 'E79': ('Models/InformationGeometry.lean', 'entropyProductionRate', 'entropyProductionRate_nonnegative'),
 'E82': ('Models/InformationGeometry.lean', 'informationMetricEntry', 'informationMetricEntry_symmetric'),
}

def ids(text, name):
    match = re.search(r'\bdef '+name+r'\s*:[^:]*?:=\s*(.*?)(?=\n(?:def |theorem |end )|\Z)',text,re.S)
    if not match: raise ValueError('missing declaration '+name)
    expr=match[1]
    result=re.findall(r'"([^"\n]+)"',re.sub(r'numberedIds\s+"[^"\n]+"\s+\d+\s+\d+','',expr))
    for stem,start,count in re.findall(r'numberedIds\s+"([^"\n]+)"\s+(\d+)\s+(\d+)',expr):
        result += [stem+str(i) for i in range(int(start),int(start)+int(count))]
    return result

def compute(root=ROOT):
    registry=(root/'WCTLean/Registry.lean').read_text()
    all_ids=sum([ids(registry,n) for n in ('masterIds','canonicalIds','electronIds','auxiliaryIds','cosmologyIds','topologyIds','correctionIds')],[])
    coverage=(root/'WCTLean/CoverageLedger.lean').read_text()
    typed=ids(coverage,'equationSpecificIds')
    if len(all_ids)!=142 or len(set(all_ids))!=142: raise ValueError('canonical registry changed')
    if len(typed)!=len(set(typed)) or not set(typed)<=set(all_ids): raise ValueError('invalid/duplicate promotion')
    remaining=[x for x in all_ids if x not in typed]
    for name,size in [('equationSpecificIds',len(typed)),('registryOnlyIds',len(remaining))]:
        if not re.search(name+r'\.length\s*=\s*'+str(size)+r'\s*:=',coverage):
            raise ValueError('Lean count differs from derived count')
    for eq,(file,*declarations) in PROMOTIONS.items():
        source=(root/'WCTLean'/file).read_text()
        if eq not in typed or any(not re.search(r'\b(?:def|theorem)\s+'+d+r'\b',source) for d in declarations):
            raise ValueError('missing substantive declaration for '+eq)
    return dict(schema='WCT_TYPED_COVERAGE_V1',registered=len(all_ids),typed=len(typed),
                registry_only=len(remaining),typed_ids=typed,registry_only_ids=remaining,
                batch_declarations=PROMOTIONS,scientific_status_changed=False)

def summary(d):
    return f"<!-- coverage-audit: registered={d['registered']} typed={d['typed']} registry_only={d['registry_only']} -->"

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--check',action='store_true');a=ap.parse_args()
    d=compute();p=ROOT/'coverage_ledger.json';serialized=json.dumps(d,indent=2)+'\n'
    if a.check:
        if p.read_text()!=serialized: raise SystemExit('coverage_ledger.json drift')
        for doc in ('FORMAL_COVERAGE_INDEX.md','THEOREMS.md','SYMPY_MAP.md'):
            if summary(d) not in (ROOT/doc).read_text(): raise SystemExit(doc+' coverage summary drift')
    else:p.write_text(serialized)
    print(f"coverage: {d['typed']}/{d['registered']}; registry-only {d['registry_only']}")
if __name__=='__main__':main()
