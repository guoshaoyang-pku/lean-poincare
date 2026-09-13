# Lean Poincare - verifier-gated formalization

![Ricci flow neck-pinch on a wireframe 3-sphere](assets/banner.png)

> A public, evidence-first workspace for formalizing the geometric and analytic layers around Perelman's proof of the Poincare conjecture in Lean 4.

[![publication branch](https://img.shields.io/badge/publication-ai4math--swarm%2Fshaoyang%2Fperelman__formulation-2b6f8e)](https://github.com/swarm-research/ai4math-swarm/tree/shaoyang/perelman_formulation)
[![compile verified](https://img.shields.io/badge/compile--verified-96%20packages-147d64)](https://github.com/swarm-research/ai4math-swarm/tree/shaoyang/perelman_formulation/perelman_formulation/release)
[![open blockers](https://img.shields.io/badge/open%20research%20blockers-24-b5472b)](https://github.com/swarm-research/ai4math-swarm/blob/shaoyang/perelman_formulation/perelman_formulation/manifest/blockers.md)
[![Lean](https://img.shields.io/badge/Lean-4.32.1-5847bf)](https://github.com/swarm-research/ai4math-swarm/blob/shaoyang/perelman_formulation/perelman_formulation/release/lean-toolchain)

This repository is the readable landing page and historical release record for the project. The active handover and publication line is ai4math-swarm/shaoyang/perelman_formulation. The swarm branch contains the integrated release overlay, current manifests, leader lanes, handoff materials and reproducible evidence. This repository keeps the stable project narrative, selected release sources and historical audit trail.

## What is proved, and what is not

The project currently contains kernel-checked definitions, model-space lemmas, conditional interfaces, implication chains and verifier artifacts. Compile-verified means that Lean compilation, per-file kernel checks, forbidden-token scans and an axiom-cone audit passed for the recorded package. It does not mean that the full Perelman proof or the Poincare conjecture has been formalized.

The major missing inputs remain analytic existence and regularity, genuine Riemannian geometry and measure constructions, entropy and noncollapsing, geometric compactness, canonical neighborhoods, surgery/extinction and the unconditional topological recognition step. A theorem with an explicit certificate or hypothesis is recorded as conditional; it is never presented as closure of the underlying blocker.

## Progress map

| layer | status | evidence |
|---|---|---|
| **M0 - toolchain and baseline** | complete | pinned Lean/mathlib, clean baseline, declaration and axiom manifests |
| **M1 - geometry** | partial | curvature, connection, Jacobi/Sturm and model-space results; general Riemann/Ricci/geodesic gaps remain |
| **M2 - heat analysis** | open frontier | Euclidean heat-kernel bridge and audits exist; general manifold existence remains open |
| **M3 - Ricci-flow producer** | open | DeTurck and short-time existence interfaces are stated, without a general inhabitant |
| **M4 - entropy and volume** | partial | finite/model-level certificates compile; analytic monotonicity inputs remain open |
| **M5-M7 - noncollapsing to surgery** | open | statement-only or conditional layers with named blockers |
| **M8 - recognition** | open | topology and geometric realization tasks remain in the DAG |

The current swarm snapshot records **96 compile-verified task packages**, a **145-node DAG**, five leader lanes and **24 named research blockers**. These are evidence indexes, not a percentage-complete claim.

## Reproduce the release

For the active package, clone the publication branch and enter its release tree:

    git clone -b shaoyang/perelman_formulation https://github.com/swarm-research/ai4math-swarm.git
    cd ai4math-swarm/perelman_formulation/release
    lake build

Use the pinned toolchain and mathlib revision in lean-toolchain and lake-manifest.json; do not update dependencies when reproducing a snapshot.

## Project documents

- [中文项目说明](docs/lean-formalization-agent-swarm-blog.zh-CN.md)
- [研究计划与 DAG](docs/lean-formalization-agent-swarm-dag.html)
- [控制面板](docs/lean-formalization-agent-swarm-control.html)
- [项目总览图](docs/lean-formalization-agent-swarm.html)
- [仓库结构](docs/REPOSITORY-STRUCTURE.md)
- [协作者 handoff](docs/TEAM-HANDOFF.md)
- [上游适配策略](docs/UPSTREAM-INTEGRATION.md)
- [Mathlib onboarding](docs/MATHLIB-ONBOARDING.md)
- [release manifest](manifest/weekly-release-manifest.md)
- [blocker ledger](manifest/blockers.md)

## Working model

The swarm publication branch is the source of truth for active work. Leaders and workers checkpoint into evidence artifacts; an integrator promotes only material that passes the compile and audit gates. Historical logs and large build caches stay out of this landing repository so a fresh reader can understand the project without downloading a multi-gigabyte runtime snapshot.

For a cold start, follow the handoff guide and then clone shaoyang/perelman_formulation. Do not treat this repository's main branch as a replacement for the swarm publication branch.
