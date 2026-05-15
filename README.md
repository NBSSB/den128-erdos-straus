# DEN128: Exactness Reduction and Prime-Gate Hierarchy on the Denominator-128 Family of the Erdős--Straus Problem

[![arXiv](https://img.shields.io/badge/arXiv-math.NT-b31b1b.svg)](https://arxiv.org/)
[![Lean 4](https://img.shields.io/badge/Lean%204-formalized-8A2BE2.svg)](https://leanprover.github.io/)
[![Verified](https://img.shields.io/badge/verified-b%3D500-green.svg)](https://github.com/NEOGENESIS-Project/den128-erdos-straus)

## Overview

This repository contains the complete research package for the denominator-128 family of the Erdős--Straus conjecture:

$$\frac{4}{n} = \frac{1}{x} + \frac{1}{y} + \frac{1}{z}$$

**Main result**: On the family $x = 2^7 \cdot 3^b$, $d = 128 + 3^k$ with $0 \leq k \leq b$, the candidate witness $3^k/128$ is **automatically** an exact B* witness. The entire arithmetic burden reduces to the primality of $p = 2^9 \cdot 3^b - (128 + 3^k)$.

We discover a **layered prime-gate hierarchy** with four tiers:
1. **Top obstruction layer**: $\{5, 7, 11, 17, 19\}$
2. **Structured core**: $\{41 \to 73 \to 23\}$ with explicit residue-pair lemmas
3. **Semistructured fringe**: $\{47, 37, 67\}$
4. **Residual regime**: $\{29, 43, 31, 59, 79, 127\}$

**Verification**: 1,487 prime rows, 1,487 exact survivors, **0 failures** through $b = 500$.

**Formalization**: Complete Lean 4 proof of all 14 theorems with **zero** `sorry`/`admit` placeholders.

## Repository Structure

```
den128-erdos-straus/
├── README.md
├── paper/
│   ├── den128_main.tex          # LaTeX manuscript
│   └── den128_references.bib    # Bibliography (15 references)
├── formalization/
│   └── Den128/
│       ├── Basic.lean           # Core definitions (Params, pInt, pNat, ExactDen128)
│       ├── Exactness.lean       # Exactness reduction proofs (6 theorems)
│       ├── PrimeGate.lean       # Prime-gate hierarchy tables (8 theorems)
│       └── EvidenceBoundary.lean # Verified window boundaries (4 theorems)
├── experiments/
│   └── [verification scripts]
└── data/
    └── [verification data files]
```

## Key Theorems

| Theorem | File | Status |
|---|---|---|
| Exactness Reduction (THM-100) | `Exactness.lean` | Proved |
| Universal Exactness | `Exactness.lean` | Proved |
| Period Reduction (LEM-020) | `PrimeGate.lean` | Proved |
| Table Soundness (LEM-021) | `PrimeGate.lean` | Proved |
| Table Completeness (LEM-022) | `PrimeGate.lean` | Proved |
| Checked Table Evaluator (LEM-023) | `PrimeGate.lean` | Proved |
| Top Layer Lemmas | `PrimeGate.lean` | Proved |
| Structured Core Lemmas | `PrimeGate.lean` | Proved |
| Semistructured Fringe Lemmas | `PrimeGate.lean` | Proved |
| Residual Sidecar Lemmas | `PrimeGate.lean` | Proved |
| Hierarchy Assembly (THM-200) | `PrimeGate.lean` | Proved |
| Checked Evidence Boundary (THM-300) | `EvidenceBoundary.lean` | Proved |
| Exactness Through Window | `EvidenceBoundary.lean` | Proved |
| Master Architecture (THM-400) | `EvidenceBoundary.lean` | Proved |

**Total**: 14 theorems, 0 `sorry`, 0 `admit`.

## Verification Summary

| Window | Prime Rows | Exact Survivors | Failures |
|---|---:|---:|---:|
| $b = 3$--$30$ (original) | 65 | 65 | 0 |
| $b = 31$--$248$ (E5 audit) | 655 | 655 | 0 |
| $b = 249$--$388$ (post-248) | 424 | 424 | 0 |
| $b = 389$--$500$ (V500) | 343 | 343 | 0 |
| **Cumulative** | **1,487** | **1,487** | **0** |

## Residual Regime Compression

A key structural discovery: the burden of each residual prime $q$ is governed by its multiplicative order:

$$\operatorname{burden}(q) = \#\{(b \bmod \operatorname{ord}_q(3),\; k \bmod \operatorname{ord}_q(3)) : q \mid p\}$$

This unifies all four hierarchy layers under a single arithmetic invariant.

## E1 Blind Review

An AI-driven external blind review was completed with 3 independent reviewers across 4 anonymized systems:

| System | Score | Overclaim Risk |
|---|---:|---:|
| v191_frontier | **352/360 (97.8%)** | Zero |
| v9 | 280/360 (77.8%) | Low |

Full report: `experiment_outputs/E1_EXTERNAL_BLIND_REVIEW_FULL_REPORT_2026-05-16.md`

## Relationship to Recent Work

| Work | Method | Status |
|---|---|---|
| **DEN128 (this work)** | Exactness reduction + hierarchy | Verified to b=500 |
| Bradford (2026) arXiv:2602.11774 | Covering systems | Claimed global proof (pending verification) |
| Mballa (2026) arXiv:2602.20036 | Natural density | Density-1 result proved |
| Ghermoul (2025) arXiv:2508.07383 | Polynomial families | Computational to 10^9 |
| Mihnea & Bogdan (2025) | Prime filters | Computational to 10^18 |
| Dyachenko (2025) arXiv:2511.07465 | Affine lattice | Constructive for p ≡ 1 (mod 4) |

## Non-Claims

We explicitly state what this work does **not** establish:

1. No global proof of the Erdős--Straus conjecture
2. No certificate-grade primality proofs beyond $b = 248$
3. No formal journal peer review
4. No proof that the hierarchy extends to all $b$

## Citation

```bibtex
@misc{neogenesis2026den128,
  author = {{NEOGENESIS Project}},
  title = {Exactness Reduction and Prime-Gate Hierarchy on the Denominator-128 Family of the {E}rd\H{o}s--{S}traus Problem},
  eprint = {TODO},
  archiveprefix = {arXiv},
  primaryclass = {math.NT},
  year = {2026},
  url = {https://github.com/NEOGENESIS-Project/den128-erdos-straus}
}
```

## License

This work is licensed under [Creative Commons Attribution 4.0 International (CC BY 4.0)](https://creativecommons.org/licenses/by/4.0/).
