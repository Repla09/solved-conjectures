# Backbite connectivity above the Dirac threshold

## The problem

A **backbite** changes a Hamiltonian path $P = v_1 v_2 \dots v_n$ of a graph $G$ by picking an endpoint, say $v_1$, and a neighbour $v_i$ of it with $i \ge 3$. It adds the edge $v_1 v_i$ and deletes the path edge $v_{i-1} v_i$, giving the Hamiltonian path $v_{i-1} \dots v_1 v_i \dots v_n$. The **reconfiguration graph** $R(G)$ has the Hamiltonian paths of $G$ (unoriented) as vertices, joined when one backbite turns one into the other.

Kazazi ([arXiv:2610.05068](https://arxiv.org/abs/2610.05068), October 2026) proved that $R(G)$ is connected when $\delta(G) \ge \lceil (2n-1)/3 \rceil$ and gave graphs with $\delta(G) = \lfloor n/2 \rfloor - 3$ and disconnected $R(G)$. He conjectured (Conjecture 7.8) that **$\delta(G) \ge n/2$ implies $R(G)$ is connected**.

## The results

**Theorem 1 (asymptotic conjecture).** For every fixed $\varepsilon > 0$ there is $n_0(\varepsilon)$ such that every graph on $n \ge n_0(\varepsilon)$ vertices with $\delta(G) \ge (1/2 + \varepsilon)\,n$ has connected $R(G)$.

With Kazazi's examples, this shows that $1/2$ is the right limiting minimum-degree ratio. Quantitatively, a surplus of $K n \log\log\log n / \sqrt{\log\log n}$ above $n/2$ suffices for an absolute constant $K$ (Section 5 of the proof).

**Theorem 2 (exact threshold, bipartite family).** If $\delta(G) \ge n/2$ and $G$ contains a spanning $K_{\lfloor n/2 \rfloor, \lceil n/2 \rceil}$, then $R(G)$ is connected. This covers every Dirac graph with an independent set of size $\lfloor n/2 \rfloor$, including $K_{h,h}$, which contains no squared Hamiltonian path.

**Theorem 3 (computer check).** The conjecture holds for every graph with at most 11 vertices.

**Lemma (descent).** If $H \subseteq G$ is a spanning subgraph with $\delta(H) \ge n/2$, every Hamiltonian path of $G$ can be backbitten into a Hamiltonian path of $H$. So the conjecture only needs checking on edge-minimal Dirac graphs, which is what makes the computer check fast.

## What is checked, and how

| Part | Method | Status |
| :--- | :--- | :-: |
| Theorems 1 and 2 | Written proof: [PROOF.md](PROOF.md) | ✅ |
| Orders $3$ to $11$, every graph with $\delta \ge \lceil n/2 \rceil$ | [`scripts/verify_dirac.py`](scripts/verify_dirac.py) with nauty's `geng` | ✅ |
| The explicit move sequences used in the proof | [`scripts/verify_moves.py`](scripts/verify_moves.py) | ✅ |

Census (graphs up to isomorphism; the last three columns show how each edge-minimal graph was certified):

| $n$ | Dirac graphs | edge-minimal | squared Hamiltonian path | cycle 2-opt moves | full path search |
| --: | --: | --: | --: | --: | --: |
| 3 | 1 | 1 | 1 | 0 | 0 |
| 4 | 3 | 1 | 0 | 1 | 0 |
| 5 | 3 | 1 | 1 | 0 | 0 |
| 6 | 19 | 4 | 0 | 3 | 1 |
| 7 | 29 | 5 | 3 | 1 | 1 |
| 8 | 424 | 17 | 7 | 8 | 2 |
| 9 | 1,165 | 32 | 29 | 1 | 2 |
| 10 | 108,376 | 483 | 384 | 82 | 17 |
| 11 | 868,311 | 2,516 | 2,493 | 15 | 8 |

```sh
brew install nauty   # or apt install nauty
cd results/backbite-dirac/scripts
for n in 3 4 5 6 7 8 9 10 11; do python3 verify_dirac.py $n; done
python3 verify_moves.py
```

Below the threshold, no counterexample appeared either: all graphs with $n = 7$, $\delta \ge 3$ and $n = 9$, $\delta \ge 4$ have connected $R(G)$ ([`scripts/backbite.py`](scripts/backbite.py) on the full `geng` output).

## The proof in brief

- **Descent:** a Dirac-type index count closes any Hamiltonian path into a cycle with one backbite, and moving the cut removes path edges outside a Dirac subgraph one at a time.
- **Core:** random sampling finds a bounded vertex set $B$ whose induced graph contains a balanced blow-up $F(t)$ of a dense graph $F$. Hamiltonian cycles of $F(t)$ correspond to Euler tours of type multigraphs. The Abrham–Kotzig theorem connects tours with the same multigraph, and an alternating-trail exchange moves any multigraph to a fixed target.
- **Growth:** the remaining vertices are added one at a time in a random order. Each new vertex has more than half the current graph as neighbours, and a lifting lemma keeps $R$ connected.

## Still open

- The exact conjecture $\delta(G) \ge n/2$ for all $n$, and even $\delta(G) \ge n/2 + C$ for a fixed constant $C$.
- Whether a threshold below $n/2$ already works. Small cases hint that it might.
