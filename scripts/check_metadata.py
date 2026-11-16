from pathlib import Path
import json, yaml, jsonschema
root=Path(__file__).resolve().parents[1]
schema=json.loads((root/'verification/formalization-v0.4.schema.json').read_text())
metadata=yaml.safe_load((root/'formalization.yaml').read_text())
jsonschema.validate(metadata,schema)
assert metadata['project']['authors']==['Wen Chang','Quanyu Tang']
assert metadata['repository']['role']=='substantive-development'
assert metadata['status']['sorry_count']==0
config=json.loads((root/'comparator.json').read_text())
solution=config['solution_module']
solution_file=solution.replace('.','/')+'.lean'
for result in metadata['status']['main_results']:
    assert result['file']==solution_file
    assert result['declaration'] in config['theorem_names']
    assert result['comparator_config']=='comparator.json'
for statement in metadata['alignment']['statements']:
    assert statement['module']==solution
    assert statement['lean'] in config['theorem_names']
citation=yaml.safe_load((root/'CITATION.cff').read_text())
assert len(citation['authors'])==2
print('PASS: formalization.yaml v0.4 schema and citation authors')
