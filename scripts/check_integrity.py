from pathlib import Path
import re, json, hashlib, sys
ROOT=Path(__file__).resolve().parents[1]
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
        holes=re.findall(r'\b(?:sorry|admit|native_decide|axiom)\b',t)
        if rel.as_posix()=='Challenge.lean':
            if holes!=['sorry']: errors.append('Challenge must have exactly one theorem hole')
            if len(s.splitlines())>1000 or len(s.encode())>102400: errors.append('Challenge size limit')
            imports=re.findall(r'^\s*(?:public )?import (\S+)',t,re.M)
            if not all(x.startswith('Mathlib.') for x in imports): errors.append('Challenge import outside Mathlib')
        elif holes: errors.append(f'Forbidden proof token: {rel}: {holes}')
conf=json.loads((ROOT/'comparator.json').read_text())
if conf.get('permitted_axioms')!=['propext','Quot.sound','Classical.choice']: errors.append('Axiom allowlist changed')
if conf.get('definition_names')!=[]: errors.append('No definition holes are allowed')
if 'external_kernels' in conf: errors.append('External kernels belong to generated local config only')
manifest=json.loads((ROOT/'lake-manifest.json').read_text())
for pkg in manifest['packages']:
    if pkg['type']!='git' or not re.fullmatch('[0-9a-f]{40}',pkg.get('rev','')): errors.append(f'Unpinned dependency: {pkg["name"]}')
for line in (ROOT/'verification/SHA256SUMS').read_text().splitlines():
    digest,name=line.split('  ',1)
    if hashlib.sha256((ROOT/name).read_bytes()).hexdigest()!=digest: errors.append(f'Checksum mismatch: {name}')
if errors:
    print('\n'.join(errors),file=sys.stderr); raise SystemExit(1)
print(f'PASS: {len(sources)} module sources, no proof holes outside Challenge, pinned Git dependencies, no private references, source checksums match')
