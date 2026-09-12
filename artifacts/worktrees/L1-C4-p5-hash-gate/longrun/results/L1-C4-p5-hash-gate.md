# L1-C4 P5 source-hash gate

Executable fail-closed source identity gate for recurring release obligation P5.

Implementation: tools/release-hash-gate.py. It parses sha256sum manifests, rejects malformed or unsafe paths, excludes .lake and .git, reports added/changed/removed files as JSON, and exits 0 only when recorded bytes match.

Tests: 9 local unit and negative-control tests passed with python3 -B -m unittest discover -s tools -p test_release_hash_gate.py -v.

Authentic D13 acceptance run: final-release-hashes.txt recorded 462 files; current D13 release had 462 files; 462 matched; 0 added, 0 changed, 0 removed; verdict PASS exit 0; manifest SHA256 bf9a8f3bbb3510d85234f6d8451e14e967c74b0412205c6a6f335a6da7c821ff.

Negative control: temporary copy with only ReleaseAudit.lean appended to; verdict FAIL exit 1; matched 461; changed path ReleaseAudit.lean; added/removed 0/0.

Semantic boundary: proved software behavior only; exact mathematical blockers closed []; P5 remains an open recurring obligation. This artifact does not prove Poincare and does not replace compile, axiom, source-hash, downstream-use or semantic gates.

No queue, credential, dispatcher, or other worktree was changed.

TASK_DONE
