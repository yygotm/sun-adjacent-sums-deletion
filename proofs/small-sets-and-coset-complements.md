# Small sets and complements of subgroup cosets

Throughout, $G$ is a finite abelian group of odd order, written additively. A *rainbow cyclic ordering* of a subset $A$ is a list of its elements, each occurring exactly once, such that the sums of consecutive vertices, including the last and first vertices, are pairwise distinct. All cyclic orderings claimed below have at least three vertices.

## 1. Statements and elementary inputs

**Theorem.** Each of the following subsets admits a rainbow cyclic ordering:

1. Every subset of size $3$, $4$, or $5$.
2. The whole group, when $|G|\ge3$.
3. The complement of one element, when $|G|\ge5$.
4. The complement of a coset of a proper subgroup, provided that complement has size greater than two.
5. Any union of exactly $3$, $4$, or $5$ cosets of one subgroup.

Sections 2–3 prove the small-set cases by cancellation and a finite graph argument. Section 4 gives the full-group and one-deletion inputs, and Section 5 proves the coset statements without requiring a splitting of the quotient map. Section 6 records a separate deduction for dense subsets from a published theorem.

We use the following two auxiliary results, with their proofs given in **two-deletion.md, Sections 3 and 4**, respectively:

- **Prescribed-edge property:** for any two distinct elements of a nontrivial finite abelian group of odd order, there is a rainbow cyclic ordering of the entire group containing that edge.
- **Subgroup extension:** if $H\le G$ is nontrivial and $B\subseteq H$ is a singleton or admits a rainbow cycle of length at least three, then $(G\setminus H)\cup B$ admits a rainbow cycle whenever its size is at least three. Its sum set is $(G\setminus H)\cup C_B$, where $C_B$ is the local sum set; for a singleton $B=\{u\}$ one sets $C_B=\{2u\}$.

The subgroup-extension statement follows there by iterating a prime-index construction along a subgroup chain. It applies to arbitrary subgroups, including those which are not direct factors. These two inputs are elementary and independent of the small-set and coset-complement results proved here.

## 2. Elementary facts and sizes 3 and 4

Multiplication by 2 is a bijection on $G$: its kernel is trivial because $G$ has odd order. In particular, $2x=2y$ implies $x=y$. Translation of every vertex by $t$ translates every edge sum by $2t$, so it preserves the property.

Color the edge $\{x,y\}$ of the complete graph on $A$ by $x+y$. Edges sharing a vertex have different colors, by cancellation.

**Four-vertex lemma.** For distinct $a,b,c,d$, at most one of

\[
a+b=c+d,\qquad a+c=b+d,\qquad a+d=b+c
\]

holds. For example, the first two imply $2(b-c)=0$, hence $b=c$, a contradiction; the other pairs follow by renaming.

**Size 3.** Any order works: any two edges of the triangle share a vertex, so cancellation distinguishes their sums.

**Size 4.** The three perfect matchings on four vertices partition the six edges. If a matching has two edges of the same color, discard it; there is at most one such matching by the lemma. If none does, discard any matching. The union of the other two matchings is a four-cycle. Its incident edges have distinct colors by cancellation, and its opposite edges have distinct colors by the choice of discarded matching. This proves the assertion.

## 3. Size 5: a complete, hand-checkable finite lemma

The labels $0,1,2,3,4$ in this section are **vertex names**, not their values in $G$. Write $ij=kl$ for a forbidden pair of edges having equal colors. It does not mean that the vertex labels are integers in a group.

For a proper coloring of $K_5$, every color class is a matching of size at most two. Thus the collection $F$ of equal-color edge pairs satisfies:

1. Each pair comprises two disjoint edges.
2. No edge appears in two members of $F$.
3. No two members of $F$ use the same four-vertex set, by the four-vertex lemma.

Call any collection satisfying these three purely combinatorial conditions *admissible*, even if it is not realized by group sums. It suffices to find a five-cycle containing neither forbidden pair in its entirety. Any cycle working for an admissible extension of $F$ also works for $F$.

Here is a complete classification of the maximal admissible collections, up to renaming vertices:

\[
\begin{aligned}
M_3&=\{01=24,\ 02=34,\ 03=14\},\\
M_5&=\{01=23,\ 02=14,\ 03=24,\ 04=13,\ 12=34\}.
\end{aligned}
\]

For completeness, the following small branching table proves the classification without relying on executable code. Name the intermediate collections

\[
\begin{aligned}
R_1&=\{01=23\},\\
R_2&=\{01=24,02=13\},\\
R_3&=\{01=34,02=14,03=12\},\\
R_4&=\{01=23,02=34,03=14,04=12\}.
\end{aligned}
\]

The complete universe of possible pairs is

```
01=23  01=24  01=34  02=13  02=14
02=34  03=12  03=14  03=24  04=12
04=13  04=23  12=34  13=24  14=23
```

Starting from the empty collection, a first pair can always be renamed to $R_1$. For each subsequent row below, exclude pairs that reuse an edge or a four-vertex set. The table lists **all** remaining possibilities. The permutation column lists the images of vertices $0,1,2,3,4$, in that order; it maps the extended collection to the named target. Thus every entry is verifiable by direct substitution.

| Current collection | Added pair | Target | Permutation |
|---|---|---|---|
| $R_1$ | 02=14 | $R_2$ | 01243 |
| $R_1$ | 02=34 | $R_2$ | 13024 |
| $R_1$ | 03=14 | $R_2$ | 01423 |
| $R_1$ | 03=24 | $R_2$ | 13204 |
| $R_1$ | 04=12 | $R_2$ | 10243 |
| $R_1$ | 04=13 | $R_2$ | 10423 |
| $R_1$ | 12=34 | $R_2$ | 31024 |
| $R_1$ | 13=24 | $R_2$ | 31204 |
| $R_2$ | 03=14 | $R_3$ | 01324 |
| $R_2$ | 04=23 | $R_3$ | 03142 |
| $R_2$ | 12=34 | $R_3$ | 21043 |
| $R_2$ | 14=23 | $M_3$ | 10432 |
| $R_3$ | 04=23 | $R_4$ | 01432 |
| $R_3$ | 13=24 | $R_4$ | 10423 |
| $R_4$ | 13=24 | $M_5$ | 01324 |
| $M_3$ | none | terminal | — |
| $M_5$ | none | terminal | — |

Every nonmaximal admissible collection can be extended until maximal, because the universe has only fifteen pairs. The table proves that a maximal collection is a relabeling of $M_3$ or $M_5$.

Finally, explicit cycles for the two terminal collections are:

| Collection | Cycle | Its five edges |
|---|---|---|
| $M_3$ | 0,1,2,3,4 | 01,12,23,34,04 |
| $M_5$ | 0,1,3,4,2 | 01,13,34,24,02 |

Inspection shows that neither list contains both edges of any forbidden pair in the corresponding collection. Applying the inverse renaming gives a rainbow five-cycle for the original $F$. This proves the $n=5$ case for all finite odd abelian groups. In fact, §§2–3 only require that the abelian group have no element of order two.

## 4. Full-group and one-element-deletion orderings

A full-group rainbow ordering follows immediately from the prescribed-edge property of **two-deletion.md, Section 3**. We give the one-deletion construction explicitly, including its cyclic and elementary-abelian inputs.

### 4.1 A cycle on the nonzero elements of an odd cyclic group

Let $m\ge5$ be odd. All entries in the following lists are interpreted modulo $m$, and every run advances by $2$ or by $-2$ as indicated. For $m=4k+1$, $k\ge1$, use

$$
Q_m=(2k+2,2k+4,\ldots,4k;\quad
2,4,\ldots,2k;\quad
2k-1,2k-3,\ldots,1;\quad
4k-1,4k-3,\ldots,2k+1).
\tag{1}
$$

For $m=4k+3$, $k\ge1$, use

$$
Q_m=(2k+2,2k+4,\ldots,4k+2;\quad
2,4,\ldots,2k;\quad
2k+1,2k-1,\ldots,1;\quad
4k+1,4k-1,\ldots,2k+3).
\tag{2}
$$

The first two runs partition the even representatives and the last two partition the odd representatives. Thus every element of $\{1,\ldots,m-1\}$ occurs once. To verify the colors, the following table lists each run's internal sums as representatives in $\{1,\ldots,m-1\}$ and the sum on the edge from that run to the next. The edge after run 4 is the closing edge. A progression of length zero is empty.

| Modulus | Run | Internal color representatives | Number | Following joining color |
|---|---:|---|---:|---:|
| $4k+1$ | 1 | $5+4j$, $0\le j<k-1$ | $k-1$ | $1$ |
| $4k+1$ | 2 | $6+4j$, $0\le j<k-1$ | $k-1$ | $4k-1$ |
| $4k+1$ | 3 | $4k-4-4j$, $0\le j<k-1$ | $k-1$ | $4k$ |
| $4k+1$ | 4 | $4k-5-4j$, $0\le j<k-1$ | $k-1$ | $2$ |
| $4k+3$ | 1 | $3+4j$, $0\le j<k$ | $k$ | $1$ |
| $4k+3$ | 2 | $6+4j$, $0\le j<k-1$ | $k-1$ | $4k+1$ |
| $4k+3$ | 3 | $4k-4j$, $0\le j<k$ | $k$ | $4k+2$ |
| $4k+3$ | 4 | $4k-3-4j$, $0\le j<k-1$ | $k-1$ | $2$ |

Each entry follows by adding the consecutive vertices in (1) or (2); the unreduced sum is the displayed value or that value plus $m$. For $m=4k+1$, the colors in residue classes $1,2,3,0$ modulo $4$ are respectively

$$
\begin{aligned}
&1,5,\ldots,4k-3; &&2,6,\ldots,4k-2;\\
&3,7,\ldots,4k-1; &&4,8,\ldots,4k.
\end{aligned}
$$

For $m=4k+3$, they are respectively

$$
\begin{aligned}
&1,5,\ldots,4k+1; &&2,6,\ldots,4k+2;\\
&3,7,\ldots,4k-1; &&4,8,\ldots,4k.
\end{aligned}
$$

These progressions are pairwise disjoint and cover $1,\ldots,m-1$ exactly once. Hence $Q_m$ has exactly the nonzero vertices and exactly the nonzero sums. The argument includes $m=5$ and $m=7$.

### 4.2 A cycle in the elementary abelian group of order nine

Let $e,f$ be a basis of $\mathbb F_3^2$. The cycle

$$
e,\ f,\ e+f,\ e+2f,\ 2e,\ 2f,\ 2e+2f,\ 2e+f
\tag{3}
$$

has successive sums

$$
e+f,\ e+2f,\ 2e,\ 2f,\ 2e+2f,\ 2e+f,\ e,\ f.
$$

Both lists are precisely the eight nonzero elements, so (3) proves the required case, including its closing edge.

### 4.3 Extension to every group of odd order at least five

Translate the deleted element to zero. If some $d\in G$ has order $m\ge5$, take $H=\langle d\rangle$ and multiply (1) or (2) by $d$. This gives a rainbow cycle on $H\setminus\{0\}$, with color set $H\setminus\{0\}$. The subgroup-extension result from **two-deletion.md, Section 4** gives the desired cycle on $G\setminus\{0\}$. When $H=G$, the local cycle already suffices.

Otherwise every nonzero element has order three. Since $|G|\ge5$, choose a nonzero $e$ and an element $f\notin\langle e\rangle$. Then $H=\langle e,f\rangle$ has order nine and is isomorphic to $\mathbb F_3^2$: the equation $ie+jf=0$, with $i,j\in\mathbb F_3$, forces $j=0$ and then $i=0$. Use (3) in $H$ and apply the same subgroup-extension result.

In either case the resulting sum set is $G\setminus\{0\}$. Translating every vertex by $a$ therefore gives a cycle on $G\setminus\{a\}$ with sum set $G\setminus\{2a\}$. This completes the one-deletion proof.

## 5. Complement equal to a subgroup coset

We first give a lifting lemma that does **not** require a splitting of the group extension.

**Lifting lemma.** Let $H\le G$, let $Q=G/H$, and let $B=\{q_0,\ldots,q_{b-1}\}\subseteq Q$ have a rainbow cyclic ordering, with $b\ge3$. Then $\pi^{-1}(B)$ has a rainbow cyclic ordering, where $\pi:G\to Q$ is the quotient map.

**Proof.** The case $H=\{0\}$ is immediate. Otherwise choose a full rainbow ordering $h_0,\ldots,h_{r-1}$ of $H$ using Section 4, and arbitrary representatives $s_i\in G$ of $q_i$. List

\[
s_0+h_0,\ldots,s_{b-1}+h_0,
s_0+h_1,\ldots,s_{b-1}+h_1,\ldots,
s_0+h_{r-1},\ldots,s_{b-1}+h_{r-1}.
\]

Every vertex in the inverse image occurs exactly once. For a fixed position $i<b-1$, its $r$ edge sums are $s_i+s_{i+1}+2h_j$, which are distinct. The $r$ boundary sums are $s_{b-1}+s_0+h_j+h_{j+1}$, also distinct. Edge sums from different positions have distinct images $q_i+q_{i+1}$ in $Q$. This proves the assertion independently of any choice of section being a homomorphism. □

**Theorem.** If $H<G$, $t\in G$, and $A=G\setminus(t+H)$ has at least three elements, then $A$ has a rainbow cyclic ordering.

**Proof.** Translate to $t=0$. Write $q=|G/H|$, an odd integer at least 3.

If $q\ge5$, Section 4 supplies a rainbow cyclic ordering of $Q\setminus\{0\}$, so the lifting lemma applies.

If $q=3$, choose $r\notin H$; the other two cosets are $r+H$ and $2r+H$, with $3r\in H$. Since $|A|=2|H|>2$, $H$ is nontrivial. Cut a full rainbow ordering of $H$, supplied by Section 4, at any edge, giving a path $h_0,\ldots,h_{s-1}$. Use the cycle

\[
r+h_0,\ldots,r+h_{s-1},
2r+h_{s-1},\ldots,2r+h_0.
\]

The internal sums in the first block lie in $2r+H$ and are distinct. Those in the second block lie in $4r+H=r+H$ and are distinct. The two joining sums are

\[
3r+2h_{s-1},\qquad 3r+2h_0.
\]

They lie in $H$, are distinct because $h_0\ne h_{s-1}$, and collide with neither block's internal sums. This proves the result. Translate back by $t$. □

The lifting lemma also proves the desired property for an arbitrary union of 3, 4, or 5 cosets of the same subgroup, by §§2–3 applied to the quotient.

The hypothesis is equality $G\setminus A=t+H$. If the removed set is only contained in one coset, the inverse-image construction does not directly apply because that coset can be partially occupied. The subgroup-extension statement in Section 1 does apply when the retained part in that coset already has a rainbow cycle or is a singleton; it does not assert such a local cycle for an arbitrary retained subset.

## 6. Dense subsets: consequence of a published theorem

This section uses a published asymptotic Hamilton-path theorem as its only non-elementary input. The preceding sections do not depend on it.

The additive abelian specialization of Müyesser–Pokrovskiy, [*A random Hall-Paige conjecture* (2025), Theorem 6.9](https://doi.org/10.1007/s00222-025-01328-x), says: for sufficiently large $N=|G|$, if distinct endpoints $x,y$ are outside $V$,

\[
|C|=|V|+1\ge N-\sqrt N,
\qquad \sum C=x+y+2\sum V,
\]

then the sum-colored graph on $V\cup\{x,y\}$, restricted to edge colors in $C$, has a rainbow Hamilton path from $x$ to $y$. Its elementary-2-group exception is irrelevant to a nontrivial odd-order group.

**Corollary.** For every sufficiently large odd $N$, every odd abelian group $G$ of order $N$ and every $A\subseteq G$ with

\[
|G\setminus A|=t,\qquad t+1\le\sqrt N
\]

have the desired rainbow cyclic ordering.

**Proof.** Increase the unspecified size threshold if necessary so $N\ge9$. Fix $z\in A$. The two sets $A$ and $2z-A$ intersect in at least $N-2t>1$ elements. Choose $x\in A\cap(2z-A)$ different from $z$, and put $y=2z-x\in A$. If $x=y$, injectivity of doubling gives $x=z$, a contradiction. Thus $x,y$ are distinct. Put $c=x+y=2z$,

\[
T=\{2a:a\in A\},\qquad C=T\setminus\{c\},
\qquad V=A\setminus\{x,y\}.
\]

Doubling is injective, so $|C|=|A|-1=|V|+1=N-t-1\ge N-\sqrt N$. Moreover,

\[
\sum C=2\sum A-c
=x+y+2\bigl(\sum A-x-y\bigr)
=x+y+2\sum V.
\]

Apply the cited path theorem. Closing the path with the edge $yx$ adds the color $c\notin C$, hence gives a rainbow cycle on exactly $A$. □

For $t=2$, the numerical density inequality holds once $N\ge9$, but the external theorem additionally requires **sufficiently large** $N$. The numerical density inequality alone does not give an explicit bound for the external theorem's threshold. For two deleted elements, **two-deletion.md, Section 5** gives an independent all-orders proof with no asymptotic hypothesis.

## 7. Scope

The small-set proof in Sections 2–3 works in every abelian group with no element of order two; finiteness is not used there. The full-group, one-deletion, and coset-complement results use finite groups of odd order. The coset-complement theorem allows quotient index three even though a two-element quotient subset cannot itself support a rainbow cycle.

The direct-factor case of two-element deletion is contained in the stronger theorem of **two-deletion.md, Section 5**, which applies to all distinct deleted pairs. None of these statements resolves Sun's conjecture for every subset of every odd-order finite abelian group.

## References

1. Z.-W. Sun, *Some new problems in additive combinatorics*, arXiv:1309.1679, Conjecture 3.3(i). https://arxiv.org/abs/1309.1679
2. R. Beals, J. A. Gallian, P. Headley, and D. Jungreis, *Harmonious groups*, Journal of Combinatorial Theory, Series A **56** (2) (1991), 223–238. https://doi.org/10.1016/0097-3165(91)90034-E
3. A. Müyesser and A. Pokrovskiy, *A random Hall–Paige conjecture*, Inventiones Mathematicae **240** (2025), 779–867, Theorem 6.9. https://doi.org/10.1007/s00222-025-01328-x
