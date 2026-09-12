import json, datetime, hashlib, os
def sha(p):
    return hashlib.sha256(open(p,'rb').read()).hexdigest()
p='checkpoint.json'
d=json.load(open(p))
now=datetime.datetime.now().strftime('%Y-%m-%dT%H:%M:%S')
d['updated_at']=now
d['status']='in_progress'
d['invocation']=7
d['elapsed_hours']=1.5
d['cumulative_task_hours']=4.45
d['round9']={
 "kernel_tautology_screen":{
  "declared_set":"audit360/taut_screen_round9.json - 339 declarations checked incl. controls; control flagged 7/7; 5 non-control flags all on def:TypeFormer/def:DataResult (result type coincides with a binder type) - over-firing class, no theorem flagged",
  "full_namespace_prop_gated":"audit360/taut_screen_full_round9.json - 1104 constants / 1061 proof-valued across 7 packages, 0 flags, control flagged 7/7, all rc 0",
  "d2d3_environment":"audit360/taut_screen_d2d3_round9.json - 1307 constants / 1179 proof-valued, 2 true positives, control flagged",
  "method":"kernel ConstantInfo: hypothesis type defeq conclusion, conclusion defeq True, or proof body an assumption-like term whose type is the flagged conclusion binder"
 },
 "new_finding_A3-D2D3-9":{
  "declaration":"Poincare.Longrun.Topology.stage6Target_of_sphereRecognition",
  "evidence":"a3d2d3/A3TautD2D3.lean rc 0 flags hypothesis-eq-conclusion:h AND proof-is-hypothesis:h",
  "class":"zero-content conditional restatement (not a soundness bug); hypothesis type is definitionally the conclusion (the missing Poincare statement)",
  "why_new":"round-3 unused-binder screen cannot catch it (hypothesis is the proof body); only the assumption-as-conclusion criterion detects it"
 },
 "drift_check":"audit360/drift_check_round8.json - independent normalized-payload comparison: 29 logs identical between rounds 7 and 8"
}
d['deliverables_sha256']={
 "longrun/results/D13-cross-audit-360-cards.md":sha('longrun/results/D13-cross-audit-360-cards.md'),
 "longrun/results/D13-cross-audit-360-cards.json":sha('longrun/results/D13-cross-audit-360-cards.json'),
 "audit360/round8_summary.json":sha('audit360/round8_summary.json'),
 "audit360/canonical_crosscheck_round8.json":sha('audit360/canonical_crosscheck_round8.json'),
 "audit360/f18_flag_classification.json":sha('audit360/f18_flag_classification.json'),
 "audit360/closure_consumption_round8.json":sha('audit360/closure_consumption_round8.json'),
 "audit360/missing_cards_recheck_round8.json":sha('audit360/missing_cards_recheck_round8.json'),
 "audit360/taut_screen_round9.json":sha('audit360/taut_screen_round9.json'),
 "audit360/taut_screen_full_round9.json":sha('audit360/taut_screen_full_round9.json'),
 "audit360/taut_screen_d2d3_round9.json":sha('audit360/taut_screen_d2d3_round9.json'),
 "audit360/drift_check_round8.json":sha('audit360/drift_check_round8.json'),
 "audit360/pkgs/D12-geometric-compactness/A3ExtraR8/PpArtifactCheck.lean":sha('audit360/pkgs/D12-geometric-compactness/A3ExtraR8/PpArtifactCheck.lean'),
 "audit360/pkgs/D12-surgery-recognition/A3ExtraR8/RegisterIdentity.lean":sha('audit360/pkgs/D12-surgery-recognition/A3ExtraR8/RegisterIdentity.lean'),
 "a3d2d3/A3TautD2D3.lean":sha('a3d2d3/A3TautD2D3.lean')
}
json.dump(d,open(p,'w'),indent=1)
print('checkpoint updated',now)
