# Every symmetric spider is 0-rotatable

## The problem

The **symmetric spider** $T(k, L)$ is a tree with one center vertex and $k$ legs, each leg a path with $L$ edges, for $q = kL$ edges in total.

A **graceful labeling** gives the vertices distinct labels from $\{0, 1, \dots, q\}$ so that the edge differences $|f(u) - f(v)|$ are exactly $1, 2, \dots, q$.

A tree is **0-rotatable** if *every* vertex can get label $0$ in some graceful labeling.

Rofa ([arXiv:2312.16235](https://arxiv.org/abs/2312.16235)) proved that symmetric spiders with $L \le 3$ are 0-rotatable and conjectured that this holds for every leg length. The case $L = 4$ was settled in [arXiv:2611.29448](https://arxiv.org/abs/2611.29448) (November 2026), where it is described as the first open case.

## The result

**Theorem.** For every $L \ge 5$ and every $k \ge 1$, the spider $T(k, L)$ is 0-rotatable.

Combined with the cases $L \le 4$ above, **every symmetric spider is 0-rotatable.**

## What is checked, and how

| Part | Method | Status |
| :--- | :--- | :-: |
| $L = 5$, all $k$ | Lean: `SpiderL5.zero_rotatable` in [`Leg5.lean`](../../SolvedConjectures/SymmetricSpiders/Leg5.lean) | ✅ |
| $L \ge 5$, all $k$ | Lean: `SpiderGeneral.zero_rotatable` in [`General.lean`](../../SolvedConjectures/SymmetricSpiders/General.lean) | ✅ |
| $L = 5$, $k \le 200$ | Python, explicit formulas: [`scripts/verify.py`](scripts/verify.py) | ✅ |
| $5 \le L \le 14$, $k \le 200$ | Python, written general construction: [`scripts/verify.py`](scripts/verify.py) `--general-through 14` | ✅ |
| $5 \le L \le 60$, $k \in \{1,2,3,6\}$ | Python, the construction used in Lean: [`scripts/check_lean_construction.py`](scripts/check_lean_construction.py) | ✅ |
| $L \le 4$ | Earlier papers (not formalized here) | from the literature |

The Lean statement of the general theorem:

```lean
theorem zero_rotatable {L k : ℕ} (hL : 5 ≤ L) (hk : 1 ≤ k) (v : ℤ)
    (hv : v ∈ Set.Icc 0 (L*(k : ℤ))) : ∃ f, Graceful L k f ∧ f v = 0
```

Vertices are numbered so a reader can check the statement directly: the center is $0$, the vertex at depth $d$ on leg $i$ is $L i + d$, and its parent is the center when $d = 1$ and $L i + d - 1$ otherwise. `Graceful L k f` says that $f$ permutes $\{0, \dots, Lk\}$ and that the edge differences $|f(x) - f(\text{parent}(x))|$ permute $\{1, \dots, Lk\}$.

## The proof in brief

- **Zero at the center:** an explicit residue-class labeling, as in Rofa's root construction.
- **Zero elsewhere:** start from a small labeled spider in which every edge crosses the center's label, then insert the remaining legs. This is the critical-label case of vertex amalgamation.
- **Odd depths:** apply the complement $x \mapsto q - x$.
- **Any vertex:** relabel the legs so the chosen vertex lies on the first leg.

For general $L$, the Lean proof builds the two path labelings it needs from explicit formulas: a reversed Walecki prefix joined to a shorter path, with two fixed sequences for exceptional positions on paths with 9 and 13 vertices. It does not rely on any earlier path-labeling theorem.

The written proof, with the $L = 5$ formulas and a second argument for all $L \ge 5$ via classical path theorems, is in [PROOF.md](PROOF.md).

## Still open

- Rofa's broader conjecture, that *every* spider (legs of different lengths) is 0-rotatable.
- The question of whether all rooted symmetric trees are 0-rotatable.
