# Zero at any vertex of a symmetric spider of leg length five

**Theorem.** For every integer $k\ge 1$, the spider $T(k,5)$ is 0-rotatable.

Write a labeling as a center value followed by rows of five labels, one row per leg in order of increasing depth. It suffices to put zero at the center or at the specified depth on the first leg, since any permutation of the legs is an automorphism. Put $q=5k$. Complementing all labels by $x\mapsto q-x$ preserves vertex bijectivity and every absolute edge difference. We construct three labelings in which 0 and $q$ occur at depths $(0,1)$, $(2,3)$, and $(4,5)$, respectively.

## A labeling with zero at the center

Use this formula also for an auxiliary spider with $n=0$ legs, consisting of its center alone. For $n\ge 0$, set the center to 0. On leg $i$, indexed from $0$ through $n-1$, put $H_i=5(n-i)$, $A_i=5i+1$ and use the row
$$
 (H_i,\ A_i,\ H_i-1,\ A_i+1,\ H_i-2).
$$
The five columns cover the positive labels through $5n$ by residue class modulo 5, with residues $0,1,4,2,3$ respectively. The center contributes the remaining label 0.

The center edges have weights $5,10,\ldots,5n$. The four internal edges of leg $i$ have weights
$$
  |5(n-2i)-r|,\qquad r=1,2,3,4.
$$
To see exactly which weights these give, write $s=n-2i$ and $B_j=\{5j+1,\ldots,5j+4\}$. For $s>0$ the four weights form $B_{s-1}$. For $s\le 0$ they form $B_{-s}$. These indices cover the required blocks exactly once. Indeed, any $0\le j<n$ with $j\equiv n-1\pmod 2$ comes from $i=(n-j-1)/2$, and every other $j$ comes from $i=(n+j)/2$. Thus every nonmultiple of 5 from 1 to $5n$ occurs once. For $n=0$ both edge sets are empty.

Taking $n=k$ gives 0 at the center and $q$ at depth 1 on the first leg. The formula follows the residue-class pattern of Rofa’s root construction. [Rofa, length-four proof, Theorem 2](https://arxiv.org/pdf/2611.29448)

## Inserting the remaining legs

Suppose a gracefully labeled spider with $s$ edges has center label $c$, and each edge has one endpoint labeled at most $c$ and the other labeled strictly above $c$. Take a second gracefully labeled spider with $m$ edges and center label 0. Identify the two centers. Keep the first spider’s labels through $c$, add $m$ to all its labels above $c$, and add $c$ to every label of the second spider.

The two prescriptions agree at the shared center. The first spider uses $[0,c]$ and $[c+m+1,s+m]$, and the second uses $[c,c+m]$. The only shared value is $c$, on the identified vertex. Every first-spider edge difference increases by exactly $m$, since only its higher endpoint moves. The differences on the second spider stay fixed under translation. The two weight sets are therefore $[m+1,m+s]$ and $[1,m]$. This also covers $m=0$, with an empty second weight set. All intervals in this proof are integer intervals. This insertion is the critical-label case of the vertex amalgamation theorem of Huang, Kotzig and Rosa. [Vertex amalgamation, Theorem 2.5](https://onlinelibrary.wiley.com/doi/full/10.1155/jama/5826777)

## The two middle depths

For $k\ge 2$ use the following two legs with center $c=4$. The first weight in each row comes from its edge to the center.

| Leg | Labels at depths 1 through 5 | Edge weights in order |
| --- | --- | --- |
| First | 7, 0, 10, 1, 9 | 3, 7, 10, 9, 8 |
| Second | 5, 3, 8, 2, 6 | 1, 2, 5, 6, 4 |

The center and rows use every label from 0 through 10. The weight rows partition 1 through 10, and each edge crosses the cut after 4. Insert the rooted spider on $n=k-2$ legs, taking $m=5(k-2)$ in the insertion rule. On the first leg the 0 at depth 2 stays fixed, and the 10 at depth 3 becomes $10+m=q$.

When $k=1$, the path with labels $(1,4,0,5,3,2)$, starting at the center, has differences $(3,4,5,2,1)$ and the same pair of extreme depths. Complementation gives zero at depth 3 in both cases.

## The last two depths

For $k\ge 1$ start with center 2 and a single leg $(3,1,4,0,5)$. The vertex labels are precisely 0 through 5. The edge differences in order are $1,2,3,4,5$, and every edge crosses the cut after 2. Insert the rooted spider on $n=k-1$ legs. Zero stays at depth 4 and the 5 becomes $5+5(k-1)=q$ at depth 5. Complementation gives zero at the leaf. This completes all six placements.

## Extension to every leg length at least five

**Theorem.** Let $L\ge5$ and $k\ge1$. For every vertex of $T(k,L)$ there is a graceful labeling assigning zero to that vertex.

The first leg will carry the largest $L$ edge weights. We make room for the other legs by increasing the high labels on this leg. Its center can now have *any* label in the low interval. A prescribed starting label on a second path compensates for the distance between the center label and the top of that interval.

### Choose two paths

Fix a depth $d\in[0,L]$ on the first leg. We use two classical path theorems, with path sizes stated in vertices.

1. Rosa’s theorem gives an $\alpha$-labeling of a path with zero at any prescribed vertex, with the sole exception of the middle vertex of the five-vertex path. An $\alpha$-labeling is graceful and has an integer cut separating the lower endpoint from the higher endpoint of every edge. Here the first leg together with the center has $L+1\ge6$ vertices. [Rosa, *Labeling snakes* (1977)](https://combinatorialpress.com/ars/vol3/) and [Panpa, Imnang and Wasuanankul, Theorem 2.1](https://onlinelibrary.wiley.com/doi/full/10.1155/jama/5826777)
2. A path with $L$ vertices has a graceful labeling with any prescribed value from $0$ through $L-1$ at its first vertex. Adding 1 to all labels gives a permutation of $[1,L]$ with any prescribed first term and absolute consecutive differences $1,\ldots,L-1$. [Cattell, *Graceful labellings of paths*](https://doi.org/10.1016/j.disc.2007.03.046) and [Ollis et al., Lemma 6.1](https://cat.middlebury.edu/~jschmitt/papers/OPPS-BHR.pdf)

Apply the first theorem at depth $d$. Orient the labels so that the center lies on the low side, complementing by $x\mapsto L-x$ if necessary. Write $g_0,\ldots,g_L$ for the result in depth order. The even positions are low. As there are $\lfloor L/2\rfloor+1$ of them, they use exactly $[0,C]$ with $C=\lfloor L/2\rfloor$. Write $c=g_0$. If $d$ is even then $g_d=0$. If $d$ is odd then $g_d=L$. This follows because the initial zero was low and the path alternates sides at every step.

Let $n=k-1$ and $m=Ln$. Keep all low labels of $g$ and add $m$ to every high label. This stretches all $L$ first-leg weights by $m$, so they form $[m+1,m+L]$. The vertex labels still to be used are exactly $[C+1,C+m]$. For $n=0$ the construction is already complete, up to the final complement below.

For $n>0$, choose by the second theorem a graceful permutation $a_1,\ldots,a_L$ of $[1,L]$ starting at
$$
a_1=L+c-C.
$$
This is an allowed first term because $0\le c\le C<L$. On additional leg $i$, for $0\le i<n$, put
$$
f(i,j)=C+a_j+
\begin{cases}
L(n-1-i), & j\text{ odd},\\
Li,       & j\text{ even},
\end{cases}
\qquad 1\le j\le L .
$$

### Check all labels and weights

For fixed $j$, the labels on the additional legs are $C+a_j+Lh$ for $0\le h<n$, each once. As $a_j$ runs through $[1,L]$, these columns tile exactly $[C+1,C+m]$. Together with the stretched first leg they give a vertex bijection onto $[0,kL]$.

The center-edge weights on the additional legs are
$$
f(i,1)-c=C+a_1+L(n-1-i)-c=L(n-i).
$$
These are all the positive multiples of $L$ through $m$.

For a fixed pair of adjacent depths on the additional legs, let $\delta$ be the odd position’s $a$-value minus the even position’s $a$-value. The corresponding weights, as the leg varies, are
$$
\big|L(n-1-2i)+\delta\big|,\qquad 0\le i<n.
$$
Replacing $i$ by $n-1-i$ negates the coefficient of $L$. Consequently the **multiset** of these weights is unchanged on replacing $\delta$ by $-\delta$. We can use $r=|\delta|$ separately for each pair of depths. Since $a$ is graceful, the $L-1$ pairs supply each $r\in[1,L-1]$ once.

It remains to account for $|Ls+r|$ with $s=n-1,n-3,\ldots,1-n$ and $1\le r<L$. Write $B_h=[Lh+1,Lh+L-1]$. For $s\ge0$ the weights give $B_s$. For $s<0$ they give $B_{-s-1}$ in reverse order. The nonnegative $s$ give the indices in $[0,n-1]$ of the same parity as $n-1$. The negative $s$ give those of the opposite parity. Thus each nonmultiple of $L$ in $[1,m]$ occurs exactly once. This accounts for every edge of the spider.

For even $d$ the selected vertex still has label 0. For odd $d$ it now has label $L+m=kL$, so complement the full labeling to put zero there. Permuting the legs gives the result for every vertex.

### A length-six example

For $L=6$, $k=3$, $d=2$, take $g=(1,5,0,6,3,4,2)$. Here $C=3$, $c=1$ and $a_1=4$. One suitable permutation is $a=(4,1,6,2,3,5)$. The resulting spider has center 1.

| Leg | Labels at depths 1 through 6 | Edge weights in order |
| --- | --- | --- |
| Selected | 17, 0, 18, 3, 16, 2 | 16, 17, 18, 15, 13, 14 |
| Additional 0 | 13, 4, 15, 5, 12, 8 | 12, 9, 11, 10, 7, 4 |
| Additional 1 | 7, 10, 9, 11, 6, 14 | 6, 3, 1, 2, 5, 8 |

The two path choices depend only on $L$ and $d$. Finite enumeration under their stated constraints is a deterministic way to find them, and the path theorems guarantee success. Once the paths are chosen, the formula takes $O(kL)$ time to produce a labeling. The specialized length-five construction above uses fixed rows and requires no enumeration.
