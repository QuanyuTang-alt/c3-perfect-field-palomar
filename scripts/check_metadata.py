from pathlib import Path
import json, yaml, jsonschema
root=Path(__file__).resolve().parents[1]
schema=json.loads((root/'verification/formalization-v0.4.schema.json').read_text())
metadata=yaml.safe_load((root/'formalization.yaml').read_text())
jsonschema.validate(metadata,schema)
assert metadata['project']['authors']==['Wen Chang','Quanyu Tang']
assert metadata['repository']['role']=='substantive-development'
assert metadata['status']['sorry_count']==0
citation=yaml.safe_load((root/'CITATION.cff').read_text())
assert len(citation['authors'])==2
print('PASS: formalization.yaml v0.4 schema and citation authors')
