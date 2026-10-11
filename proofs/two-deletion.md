# Two-element deletion in finite abelian groups of odd order

The theorem below is proved by an explicit subgroup construction. Its only induction is the proof of Property E in Section 3; each induction call uses a proper subgroup. All group operations are written additively.

## Statement and terminology

**Theorem.** Let $G$ be a finite abelian group of odd order at least five, and let $a,b\in G$ be distinct. There is a cyclic ordering of $G\setminus\{a,b\}$ in which all adjacent sums, including the last-to-first sum, are distinct.

In fact, the construction gives the exact sum set

$$
G\setminus\{3a-b,\ 3b-a\}.
$$

The two omitted colors are distinct, since their difference is $4(a-b)\ne0$ in a group of odd order. The exact-color refinement is justified at the end of §5.

We call such a cyclic ordering *rainbow*. Addition in all subgroups and quotients is inherited from $G$. In an odd finite group, doubling is bijective.

The proof uses a slightly stronger auxiliary property:

**Property E.** Every pair of distinct elements of a group occurs as an adjacent pair in some rainbow cyclic ordering of the entire group.

This property is needed for full cosets only, not for the subset containing the holes.

## 1. Two elementary preparations

### 1.1 Cutting a specified edge

Suppose an odd finite abelian group $H$ has Property E. For any distinct $u,v\in H$, it has a Hamilton path from $u$ to $v$ whose internal adjacent sums are exactly

$$
H\setminus\{u+v\}.
$$

Indeed, take a rainbow cycle on all of $H$ containing the edge $\{u,v\}$ and delete that edge. A full rainbow cycle has exactly $|H|$ distinct sums in $H$, so its sums are all of $H$. Translation gives the corresponding statement in any coset $x+H$: prescribed distinct endpoints $u,v\in x+H$ admit a spanning path with sums exactly

$$
(2x+H)\setminus\{u+v\}.
$$

### 1.2 Sums of an even number of nonzero elements

Let $H$ be a nontrivial odd finite abelian group. Every $t\in H$ is a sum of any prescribed positive even number $2s$ of nonzero elements of $H$.

For two terms, choose $c\in H\setminus\{0,t\}$, which is possible since $|H|\ge3$, and use $c+(t-c)$. Both terms are nonzero. For more terms append pairs $z,-z$, with $z\ne0$.

The terms need not be distinct. They will specify endpoint differences in different cosets; no distinctness between these differences is required.

## 2. Cyclic-quotient gluing

**Lemma.** Let $H<G$ be a nontrivial subgroup such that $G/H$ is cyclic of odd order $q\ge3$. Suppose that $H$ has Property E. Let $B\subseteq H$ be either:

1. a set of at least three elements with a rainbow cyclic ordering; or
2. a singleton.

Then

$$
(G\setminus H)\cup B
$$

has a rainbow cyclic ordering. Moreover, if a prescribed linear presentation of the cycle on $B$ is supplied, every internal edge of that presentation remains an edge of the resulting cycle.

**Proof.**

For the first case, cut the supplied cycle on $B$ at its closing edge, and denote the resulting path by $P_0$, with first vertex $u$ and last vertex $v$. Put $s_0=u+v$. The internal sums of $P_0$ are distinct and do not equal $s_0$.

For a singleton $B=\{u\}$, set $P_0=(u)$, $v=u$, and $s_0=2u$. It has no internal edges. We are not asserting a Sun-type cycle on a singleton: $s_0$ is just the color reserved for one later joining edge.

Choose $r\in G$ whose image generates $G/H$. We do **not** assume $qr=0$; all we know is $qr\in H$. Put $\delta_0=v-u$.

By §1.2, choose nonzero elements $\delta_1,\ldots,\delta_{q-1}\in H$ satisfying

$$
\delta_1+\cdots+\delta_{q-1}=-qr-\delta_0.
\tag{1}
$$

This is possible because $q-1$ is positive and even. Define

$$
x_0=u,\qquad
y_i=x_i+\delta_i,\qquad
x_{i+1}=y_i+r
\quad(0\le i<q).
\tag{2}
$$

Equation (1) gives $x_q=x_0$. Also $y_0=v$, and $x_i,y_i\in ir+H$ for every $i$. From now on, extend $x_i,y_i$ periodically with period $q$. The equality $x_q=x_0$ is an equality in $G$, so $x_{i+1}=y_i+r$ remains valid at the cyclic seam; it is not merely an equality in the quotient.

For every $i=1,\ldots,q-1$, the endpoints $x_i,y_i$ are distinct because $\delta_i\ne0$. By §1.1, choose a spanning path $P_i$ in $ir+H$ from $x_i$ to $y_i$ whose internal sums are exactly

$$
(2ir+H)\setminus\{s_i\},
\qquad s_i=x_i+y_i.
\tag{3}
$$

Place the paths in the order

$$
P_0,\ P_2,\ P_4,\ \ldots
\quad\text{with indices increasing by 2 modulo }q,
\tag{4}
$$

and close the last path back to the first. Since $q$ is odd, this visits every path exactly once.

The edge joining $P_i$ to $P_{i+2}$ has sum

$$
y_i+x_{i+2}
=(x_{i+1}-r)+x_{i+2}
=x_{i+1}+(x_{i+2}-r)
=x_{i+1}+y_{i+1}
=s_{i+1}.
\tag{5}
$$

In particular, the final joining edge in (4) is from $P_{q-2}$ to $P_0$ and has color $s_{q-1}$; the joining edge from $P_{q-1}$ to $P_1$ has color $s_0$. Thus the joining edges supply each reserved color $s_j$ exactly once. They fill the missing color of every full-coset path, and supply precisely the closing-edge color of $P_0$.

More explicitly, for every nonzero index $j$, the internal edges of $P_j$ together with the joining edge of color $s_j$ use every element of $2jr+H$ once. For index zero, they use the distinct sums of the original cycle on $B$, or just the one color $2u$ when $B$ is a singleton. Different indices give different cosets $2jr+H$, since doubling is a permutation of the odd cyclic quotient. Hence no sums collide.

The vertex sets of the paths are disjoint, and they cover exactly $(G\setminus H)\cup B$. All internal edges of $P_0$ are retained by concatenation. The complete sum set is therefore

$$
(G\setminus H)\cup C_B,
$$

where $C_B$ is the sum set of the input cycle, or $C_B=\{2u\}$ for the singleton $B=\{u\}$. This proves the lemma. □

**Non-split extensions and singleton fibers.**

- A non-split extension contributes the term $qr$ in (1). It is absorbed in the freely chosen sum of nonzero endpoint differences; no complement to $H$ is needed.
- If $H$ has order three and two elements are deleted, $B$ is a singleton. The singleton case above handles it without requiring four distinct vertices in $H$.

## 3. Every odd finite abelian group has Property E

We prove the assertion for nontrivial groups by strong induction on their order. Translation reduces the specified edge to $\{0,d\}$ with $d\ne0$. A cycle can be oriented and rotated to start with $0,d$.

**Prime order.** If $|G|=p$ is prime, the cycle

$$
0,d,2d,\ldots,(p-1)d
$$

contains the specified edge and has sums $(2i+1)d$, for $0\le i<p$ with indices modulo $p$. They are all distinct because $p$ is odd.

**Composite order.** Choose a maximal proper subgroup $H$ of $G$. Since $G$ is finite abelian, $G/H$ is cyclic of prime order $p$. Both $p$ and $|H|$ are odd, and $|H|\ge3$. The induction hypothesis gives Property E for $H$.

There are two cases.

### Case I: $d\in H$

Take a rainbow full cycle on $H$ starting with $0,d$, using the induction hypothesis. Regard it as a linear path starting with those same two vertices; the deleted closing edge is not $\{0,d\}$ because $|H|\ge3$.

Apply the gluing lemma to $G,H$ with $B=H$ and this path as $P_0$. The result is a rainbow cycle on all of $G$, and it retains the internal edge $\{0,d\}$.

### Case II: $d\notin H$

Then $d+H$ generates the prime-order quotient. Choose any rainbow full cycle

$$
h_0,h_1,\ldots,h_{m-1}
$$

on $H$, rotated so $h_0=0$. Such a cycle exists by Property E for $H$. Use the following row-by-row sequence:

$$
\begin{aligned}
&h_0,\ h_0+d,\ \ldots,\ h_0+(p-1)d,\\
&h_1,\ h_1+d,\ \ldots,\ h_1+(p-1)d,\\
&\hspace{35mm}\vdots\\
&h_{m-1},\ h_{m-1}+d,\ \ldots,\ h_{m-1}+(p-1)d.
\end{aligned}
\tag{6}
$$

It starts with $0,d$ and uses every element of $G$ once, since $0,d,\ldots,(p-1)d$ are coset representatives.

For any fixed internal position $i=0,\ldots,p-2$, its sums are

$$
2h_j+(2i+1)d\qquad(0\le j<m),
$$

which run through one entire coset of $H$. The row-boundary sums are

$$
h_j+h_{j+1}+(p-1)d\qquad(0\le j<m),
$$

also running through an entire coset of $H$; here $h_m=h_0$ includes the final closing edge. These $p$ cosets are distinct: their quotient labels are $2i+1$ for $0\le i<p-1$, together with $p-1\equiv2(p-1)+1\pmod p$.

Consequently (6) is a rainbow cycle on $G$ containing the required edge.

This completes the induction and proves Property E for every nontrivial odd finite abelian group. □

**Dependency check.** The gluing lemma in §2 assumes Property E only for its proper subgroup $H$. In this induction, that assumption is supplied by the smaller-order induction hypothesis. Neither the gluing lemma nor this induction uses the two-deletion theorem.

## 4. Extension from an arbitrary nontrivial subgroup

**Corollary.** Let $H\le G$ be a nontrivial subgroup of an odd finite abelian group. Suppose $B\subseteq H$ is a singleton or has a rainbow cyclic ordering with at least three vertices. Then $(G\setminus H)\cup B$ has a rainbow cyclic ordering whenever this resulting set has at least three vertices.

If $H=G$, the nonsingleton assertion is the hypothesis, and the singleton case has resulting size one and is excluded.

Otherwise, take a subgroup chain

$$
H=H_0<H_1<\cdots<H_t=G
$$

such that each $H_{i+1}/H_i$ has prime order. Such a chain is obtained from a composition series of the finite abelian quotient $G/H$.

Apply §2 successively. Its Property E hypothesis for every $H_i$ is now established by §3. After the first extension of a singleton the set has at least

$$
(3-1)\cdot3+1=7
$$

vertices, so subsequent steps use ordinary cycles. At stage $i$, the set is exactly $(H_i\setminus H)\cup B$. The final stage is the claimed set. □

## 5. Proof of the two-deletion theorem

Translate the holes $a,b$ by $-a$, and put $d=b-a\ne0$. Let

$$
H=\langle d\rangle,\qquad m=|H|.
$$

The order $m$ is odd and at least three.

If $m=3$, then

$$
H\setminus\{0,d\}=\{2d\}
$$

is a singleton. Since $|G|\ge5$, in this case $H$ is proper. Apply §4 to this singleton.

If $m\ge5$, use the cyclic ordering

$$
2d,3d,\ldots,(m-1)d
\tag{7}
$$

of $H\setminus\{0,d\}$. Its internal sums are $(2i+1)d$ for $2\le i\le m-2$, and its closing sum is $(m+1)d=d$. The internal sums are distinct because multiplication by 2 is invertible modulo $m$. None equals $d$: that equality would imply $2i\equiv0\pmod m$, hence $i\equiv0\pmod m$, outside the indicated range. Thus (7) is rainbow. Apply §4, or simply use (7) if $H=G$.

The resulting vertex set is

$$
(G\setminus H)\cup(H\setminus\{0,d\})
=G\setminus\{0,d\}.
$$

Translating every vertex by $a$ adds $2a$ to every adjacent sum and preserves their distinctness. This proves the theorem for the original holes $a,b$. □

**Exact omitted colors.** In (7), the internal sums are obtained from the full step-$d$ cycle by omitting the three positions $i=0,1,m-1$, whose sums are $d,3d,-d$. The new closing sum puts $d$ back. Thus precisely $-d,3d$ are absent. When $m=3$, the singleton's reserved color is $4d=d$, and the same missing-color description $\{-d,3d\}=\{2d,0\}$ holds.

In every gluing step, all colors outside the distinguished subgroup are added, and the colors inside it remain exactly those of the supplied cycle (or the singleton's reserved color). This follows from (3)–(5), since the nonzero quotient indices also remain nonzero under doubling. Hence the two absent colors stay $-d,3d$ throughout the subgroup chain. Translation by $a$ turns them into $2a-d=3a-b$ and $2a+3d=3b-a$, as asserted.

For a concrete nonsplit example, for holes $0,3$ in $\mathbb Z_9$ the construction gives

$$
6,2,8,5,7,4,1,
$$

with adjacent sums $8,1,4,3,2,5,7$, missing exactly $0,6$. This also illustrates an order-three hole difference and the singleton starting fiber.

## 6. Relation to harmonious orderings

A rainbow cyclic ordering of the whole group is usually called a harmonious ordering. Full and one-element-deletion harmonious orderings occur in the work of Beals, Gallian, Headley, and Jungreis. The proof above supplies every auxiliary existence statement it uses and does not invoke a large-order threshold or a finite search.

The conclusion is a special case of Sun's Conjecture 3.3(i), together with an exact description of the two absent sums. It does not establish the conjecture for arbitrary subsets.

## References

1. Z.-W. Sun, *Some new problems in additive combinatorics*, arXiv:1309.1679, Conjecture 3.3(i). https://arxiv.org/abs/1309.1679
2. R. Beals, J. A. Gallian, P. Headley, and D. Jungreis, *Harmonious groups*, Journal of Combinatorial Theory, Series A **56** (2) (1991), 223–238. https://doi.org/10.1016/0097-3165(91)90034-E
