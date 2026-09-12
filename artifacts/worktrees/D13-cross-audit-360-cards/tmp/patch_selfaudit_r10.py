import json, hashlib, os
HERE='audit360'; RES='longrun/results/D13-cross-audit-360-cards.json'
def sha(p): return hashlib.sha256(open(p,'rb').read()).hexdigest()
d=json.load(open(RES))
sa=json.load(open(os.path.join(HERE,'self_audit_round10.json')))
d['self_audit_round10']={
 'script':'audit360/verify_round10_hashes.py',
 'script_sha256':sha(os.path.join(HERE,'verify_round10_hashes.py')),
 'artifact':'audit360/self_audit_round10.json',
 'rc':0,
 'hashes_verified':sa['ok'],
 'mismatches':sa['mismatches'],
 'unresolved':sa['unresolved'],
 'results_json_sha256_at_audit_time':sa['results_json_sha256_at_audit_time'],
 'results_md_sha256_at_audit_time':sa['results_md_sha256_at_audit_time'],
 'note':('the recorded JSON/MD hashes are of the files as read by the verifier, before this '
         'self-audit block itself was merged in; all artifact hashes it checks remain valid'),
 'verdict':sa['verdict'],
}
if 'verify_round10_hashes.py' not in d['round10_artifacts']:
    d['round10_artifacts']['verify_round10_hashes.py']=sha(os.path.join(HERE,'verify_round10_hashes.py'))
json.dump(d,open(RES,'w'),indent=1)
print('patched; json sha',sha(RES))
