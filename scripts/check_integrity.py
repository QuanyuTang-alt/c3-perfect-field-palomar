from pathlib import Path
import re, json, hashlib, sys
ROOT=Path(__file__).resolve().parents[1]
conf=json.loads((ROOT/'comparator.json').read_text())
def module_path(name):
    if not re.fullmatch(r'[A-Za-z_][A-Za-z0-9_]*(?:\.[A-Za-z_][A-Za-z0-9_]*)*',name):
        raise ValueError(f'Invalid module name: {name}')
    return Path(name.replace('.','/')+'.lean')
challenge_name=conf['challenge_module']
solution_name=conf['solution_module']
challenge_path=module_path(challenge_name)
solution_path=module_path(solution_name)
def without_comments(s):
    out=[]; i=0; depth=0
    while i<len(s):
        if s.startswith('/-',i): depth+=1; i+=2
        elif depth and s.startswith('-/',i): depth-=1; i+=2
        elif depth: i+=1
        elif s.startswith('--',i):
            j=s.find('\n',i); i=len(s) if j<0 else j
        else: out.append(s[i]); i+=1
    if depth: raise ValueError('Unclosed comment')
    return ''.join(out)
errors=[]; sources=[]
for p in sorted(ROOT.rglob('*')):
    rel=p.relative_to(ROOT)
    if '.lake' in rel.parts or '.git' in rel.parts: continue
    if p.is_symlink(): errors.append(f'Symlink: {rel}'); continue
    if not p.is_file(): continue
    if p.suffix in ['.tex','.pdf','.olean','.ilean','.ir']: errors.append(f'Excluded artifact: {rel}')
    if p.suffix not in ['.lean','.md','.toml','.json','.yaml','.yml','.cff','.py','.sh']: continue
    s=p.read_text(encoding='utf-8')
    if re.search(r'/'+r'Users/|/'+r'home/|agent_'+r'mode|Down'+r'loads/|gh[pousr]_[A-Za-z0-9]{20,}|github_'+r'pat_',s): errors.append(f'Private reference: {rel}')
    if p.suffix=='.lean':
        t=without_comments(s); sources.append(rel.as_posix())
        if not re.match(r'\s*module\b',t): errors.append(f'Not a module: {rel}')
        if len(s.splitlines())>10000: errors.append(f'Too long: {rel}')
        holes=re.findall(r'\b(?:sorry|admit|native_decide|axiom|unsafe)\b|Lean\.ofReduceBool',t)
        if rel==challenge_path:
            if holes!=['sorry']: errors.append('Challenge must have exactly one theorem hole')
            if len(s.splitlines())>1000 or len(s.encode())>102400: errors.append('Challenge size limit')
            imports=re.findall(r'^\s*(?:public )?import (\S+)',t,re.M)
            if not all(x.startswith('Mathlib.') for x in imports): errors.append('Challenge import outside Mathlib')
        elif holes: errors.append(f'Forbidden proof token: {rel}: {holes}')
if not (ROOT/challenge_path).is_file(): errors.append('Challenge module is missing from this repository')
if not (ROOT/solution_path).is_file(): errors.append('Solution module is missing from this repository')
if conf.get('permitted_axioms')!=['propext','Quot.sound','Classical.choice']: errors.append('Axiom allowlist changed')
if conf.get('definition_names')!=[]: errors.append('No definition holes are allowed')
if 'external_kernels' in conf: errors.append('External kernels belong to generated local config only')
manifest=json.loads((ROOT/'lake-manifest.json').read_text())
for pkg in manifest['packages']:
    if pkg['type']!='git' or not re.fullmatch('[0-9a-f]{40}',pkg.get('rev','')): errors.append(f'Unpinned dependency: {pkg["name"]}')
checksum_entries={}
for line in (ROOT/'verification/SHA256SUMS').read_text().splitlines():
    digest,name=line.split('  ',1)
    if name in checksum_entries: errors.append(f'Duplicate checksum entry: {name}')
    checksum_entries[name]=digest
    if hashlib.sha256((ROOT/name).read_bytes()).hexdigest()!=digest: errors.append(f'Checksum mismatch: {name}')
if set(checksum_entries)!=set(sources): errors.append('Checksum inventory does not cover exactly all local Lean sources')
origins=json.loads((ROOT/'verification/module-origins.json').read_text())
if len({x['path'] for x in origins})!=len(origins) or {x['path'] for x in origins}!=set(sources):
    errors.append('Module origins must cover each local Lean source exactly once')
for entry in origins:
    if hashlib.sha256((ROOT/entry['path']).read_bytes()).hexdigest()!=entry['sha256']:
        errors.append(f'Module-origin hash mismatch: {entry["path"]}')
vendor=json.loads((ROOT/'verification/vendor-tauceti.json').read_text())
paths={x['path'] for x in vendor['modules']}
if vendor['module_count']!=len(vendor['modules']) or len(paths)!=len(vendor['modules']):
    errors.append('Tau Ceti provenance count or uniqueness mismatch')
if paths!={name for name in sources if name.startswith('TauCeti/')}:
    errors.append('Tau Ceti provenance must cover exactly all vendored modules')
for entry in vendor['modules']:
    if hashlib.sha256((ROOT/entry['path']).read_bytes()).hexdigest()!=entry['release_sha256']:
        errors.append(f'Tau Ceti release hash mismatch: {entry["path"]}')
    for field in ['upstream_sha256','initial_adaptation_sha256','release_sha256']:
        if not re.fullmatch('[0-9a-f]{64}',entry[field]): errors.append(f'Invalid provenance hash: {entry["path"]}')
if not re.fullmatch('[0-9a-f]{40}',vendor['upstream_commit']): errors.append('Unpinned Tau Ceti source revision')
mathlib_rev=next(p['rev'] for p in manifest['packages'] if p['name']=='mathlib')
if vendor['release_mathlib_commit']!=mathlib_rev: errors.append('Tau Ceti release Mathlib revision mismatch')
challenge=without_comments((ROOT/challenge_path).read_text()).split('namespace PalomarC3',1)[0]
statement=without_comments((ROOT/'C3PerfectField/MainStatement.lean').read_text())
if re.sub(r'\s+','',challenge)!=re.sub(r'\s+','',statement):
    errors.append('Challenge definitions differ from the production statement definitions')
seen=set(); work=[solution_name]
while work:
    name=work.pop()
    if name in seen: continue
    path=ROOT/(name.replace('.','/')+'.lean')
    if not path.exists(): continue
    seen.add(name)
    text=without_comments(path.read_text())
    work.extend(re.findall(r'^\s*(?:public\s+)?import\s+(?:all\s+)?([\w.]+)',text,re.M))
if challenge_name in seen: errors.append('Challenge must not be imported by Solution')
for kind,name in [('Challenge',challenge_name),('Solution',solution_name)]:
    top=name.split('.')[0]
    for pkg in manifest['packages']:
        dep=ROOT/manifest.get('packagesDir','.lake/packages')/pkg['name']
        if not dep.is_dir():
            errors.append(f'Dependency unavailable for module collision audit: {pkg["name"]}')
            continue
        if (dep/top).exists() or (dep/(top+'.lean')).exists():
            errors.append(f'{kind} top-level module {top} is shadowed by dependency {pkg["name"]}')
if errors:
    print('\n'.join(errors),file=sys.stderr); raise SystemExit(1)
print(f'PASS: {len(sources)} module sources, no proof holes outside Challenge, pinned Git dependencies, no private references, source checksums match')
