# Proof Package

## Claim

For every pair of coprime positive integers $a,b$, let $S=\{0,a,2a,2a+b,2a+2b\}$. An $S$-packing center set is a set $A\subseteq\mathbb Z$ for which all translates $x+S$ ($x\in A$) are pairwise disjoint. Define

$$
\overline d(A)=\limsup_{N\to\infty}\frac{|A\cap[-N,N]|}{2N+1},
\qquad d_p(S)=\sup\{\overline d(A):A\text{ is an }S\text{-packing center set}\}.
$$

Write $a-b=5q+r$ with $q\in\mathbb Z$ and $0\le r\le4$. Then

$$
d_p(S)=R(a,b):=\begin{cases}
1/5,&r=0,\\
(b+2q)/(2a+3b),&r=1,2,\\
\bigl(a-2(q+1)\bigr)/(3a+2b),&r=3,4.
\end{cases}
$$

The upper bound applies to every center set, without periodicity or existence of a density limit. A periodic center set attains the right side with an actual symmetric density limit.

## Status

**PROVABLE AS STATED.** The original assumptions and conclusion are preserved. The self-contained typeset proof is `main.tex`. This is a mathematical proof status, not a claim of complete proof-assistant formalization.

## Assumptions

- $a,b$ are fixed positive integers with $\gcd(a,b)=1$.
- $A$ is an arbitrary subset of $\mathbb Z$ satisfying the stated disjointness condition.
- Density means symmetric upper density of centers, with the limit taken over integer $N\to\infty$ after fixing $a,b,A$.
- The reduction $a>b$ is used only for the nonzero-remainder upper bound, after an explicit symmetry argument. The lower construction permits either order and negative $q$.

## Notation

- $[u,v)=\{z\in\mathbb Z:u\le z<v\}$ for integer endpoints.
- $M=\{ia+jb:0\le i,j\le2,\ i+j>0\}$ is a set of numerical values; repeated representations do not count twice.
- $h=a+b$, $n_1=2a+3b$, $n_2=3a+2b$, and $F_i=|A\cap[0,n_i)|$.
- $W$ consists of the six arrangements of two $a$-steps and two $b$-steps. For $w=(d_1,d_2,d_3,d_4)$, put $p_0=0$, $p_j=d_1+\cdots+d_j$, and $P_w=\{p_0,\ldots,p_4\}$.
- $\mathbf1_E$ denotes the indicator function of $E$.
- $e$ is a nonnegative integer in the equality lemma. In the lower construction, $t,p,u,z$ are signed integers, $g=a-b$, $n=2a+3b$, and $c=b+2q$.

## Proof Strategy

Convert packing to avoidance of the exact positive difference set. Average over six translated paths to obtain a two-window inequality; analyze its equality case to obtain a parity restriction. Integer rounding then provides a good window of one of two bounded lengths at every starting point. A greedy interval decomposition gives a uniform finite-interval estimate and hence the required upper limit. Match it with the periodic construction from Natalchenko–Sagdeev, verified directly.

## Dependency Map

1. Exact positive differences give packing–avoidance equivalence and parameter-exchange symmetry.
2. Path differences belong to $M$; the path identity therefore gives $F_1+F_2\le h$ and saturation of every indexed path at equality.
3. Saturation of three selected path types gives $F_1\equiv b\pmod2$ at equality.
4. The local inequality, equality parity, integer-valued counts, and two explicit cross products give the four-remainder good-window statement.
5. Translation invariance and bounded-length interval decomposition give the symmetric upper density bound for every $A$.
6. Coprimality and Euclidean division exclude collisions in the source's periodic construction, giving the matching lower bound.
7. The zero-remainder branch uses the five-point counting bound and a complete residue system modulo $5$.

Finite computations are supplementary and are not premises in this dependency map.

## Proof

### Step 1. Exact reformulation and symmetry

The positive differences of $S$ are

$$
\{a,2a,b,2b,a+b,a+2b,2a+b,2a+2b\}=M.
$$

Indeed, listing differences from $0,a,2a,2a+b$ gives precisely these values. Two distinct translates intersect exactly when their center difference is a nonzero element of $S-S$. Thus packing is equivalent to avoiding absolute differences in $M$.

Exchanging $a,b$ leaves $M$ unchanged. For $r\ne0$ it sends $(q,r)$ to $(-q-1,5-r)$. Substitution interchanges the two nonzero branches of $R$ without changing their values. The zero branch is invariant. Therefore the nonzero-remainder upper bound may be proved with $a>b$.

### Step 2. Zero remainder

The disjoint five-point translates with centers in $[-N,N]$ all lie in $[-N,N+2a+2b]$. Hence

$$
5|A\cap[-N,N]|\le2N+2a+2b+1,
$$

and $\overline d(A)\le1/5$. If $r=0$, write $a\equiv b\equiv v\pmod5$. Coprimality gives $v\ne0$, so the residues of $S$ are the five distinct classes $0,v,2v,3v,4v$. The center set $5\mathbb Z$ is valid and has density $1/5$. The only coprime case with $a=b$ is $(1,1)$ and is included here.

### Step 3. Path identity

Assume $a>b$. Each $P_w$ has five distinct points, and the difference of any two is a sum of a nonempty consecutive part of $w$, so lies in $M$. Each translated path contains at most one point of $A$.

The following equality is pointwise on $\mathbb Z$:

$$
\sum_{w\in W}\sum_{t=0}^{d_4-1}\mathbf1_{t+P_w}
=3\mathbf1_{[0,n_1)}+3\mathbf1_{[0,n_2)}.
$$

To prove it, expand the left side as $\sum_{j=0}^4\sum_w\mathbf1_{[p_j,p_j+d_4)}$. For fixed $0\le j\le3$, exchanging positions $j+1$ and $4$ is a bijection of $W$ preserving the first $j$ steps and hence $p_j$. It replaces $d_4$ by $d_{j+1}$. The corresponding four intervals for each word partition $[0,2h)$, giving $6\mathbf1_{[0,2h)}$. The endpoint $p_4=2h$ contributes three intervals of length $a$ and three of length $b$. This is exactly the right side.

Sum over $A$. There are $3a+3b$ indexed paths, each with intersection size at most one. Therefore $F_1+F_2\le h$. If equality holds, every indexed path must have intersection size exactly one. All sums here have finite support, even for infinite $A$.

### Step 4. Equality parity

Suppose $F_1+F_2=h$, and put $x_z=\mathbf1_A(z)$. For each $0\le u<a$, the paths

$$
u+P_{abba}=u+\{0,a,h,a+2b,2h\},\qquad
u+P_{baba}=u+\{0,b,h,a+2b,2h\}
$$

both have intersection size one. Subtraction gives $x_{u+a}=x_{u+b}$. After summing and cancelling the common interval $[a,h)$, using $b<a<h<2a$, we obtain

$$
|A\cap[b,a)|=|A\cap[h,2a)|=:e.
$$

The $b$ paths $u+P_{aabb}=u+S$, $0\le u<b$, also each have one point of $A$. They are disjoint: their five point layers are the disjoint intervals $[0,b)$, $[a,h)$, $[2a,2a+b)$, $[2a+b,2a+2b)$, $[2a+2b,2a+3b)$. Their union's complement in $[0,n_1)$ is exactly $[b,a)\cup[h,2a)$. Consequently $F_1=b+2e$ and $F_2=a-2e$.

### Step 5. Four residue cases

For $a>b$ and $r\ne0$ we have $q\ge0$.

If $r=1,2$, then $F_1\le b+2q$ or $F_2\le b+3q$. Otherwise the integer counts would satisfy $F_1+F_2\ge h+2-r$. For $r=1$ this exceeds $h$; for $r=2$ it forces equality and $F_1=b+2q+1$, violating Step 4. Set $\rho=(b+2q)/n_1$. Since

$$
(b+2q)n_2-(b+3q)n_1=br>0,
$$

either alternative gives some $F_i\le\rho n_i$.

If $r=3,4$, then $F_1\le a-3(q+1)$ or $F_2\le a-2(q+1)$. Failure of both gives $F_1+F_2\ge h+r-3$. For $r=4$ this exceeds $h$; for $r=3$ equality forces $F_1=a-3(q+1)+1=b+2q+1$, again violating Step 4. Set $\rho=(a-2(q+1))/n_2$. The identity

$$
\bigl(a-2(q+1)\bigr)n_1-\bigl(a-3(q+1)\bigr)n_2=a(5-r)>0
$$

again converts either alternative to $F_i\le\rho n_i$. In both cases $\rho=R(a,b)>0$: its numerator is respectively $b+2q$ or $b+3q+r-2$.

### Step 6. Global density bound

Translate the preceding argument by any $x\in\mathbb Z$. Because differences are unchanged, some $\ell\in\{n_1,n_2\}$ satisfies $|A\cap[x,x+\ell)|\le\rho\ell$.

Starting at $-N$, repeatedly choose such a window while the remaining part of $[-N,N+1)$ has length at least $n_2$. The positive lengths ensure termination, and $n_1\le n_2$ ensures each chosen window fits. If the remainder has length $s$, then $0\le s<n_2$ and

$$
|A\cap[-N,N]|\le\rho(2N+1-s)+s
\le\rho(2N+1)+n_2.
$$

This includes the case in which no window is selected. The error is independent of $A,N$ for fixed parameters. Divide by $2N+1$ and take the upper limit to get $\overline d(A)\le R(a,b)$. Taking the supremum over all $A$ and using Step 1 covers both orders of $a,b$. No limit is exchanged with a supremum.

### Step 7. Periodic construction, including negative quotients

This construction is due to [Natalchenko–Sagdeev, Section 2](https://arxiv.org/abs/2407.01101v2). Suppose $r=1,2$, with no order restriction on $a,b$. Put $g=a-b$, $n=2a+3b$, $c=b+2q=(n-2r)/5$. This is a positive integer because $n\ge5>2r$. Define $A_0=\{tg:0\le t<c\}+n\mathbb Z$.

Consider

$$
tg=ia+jb+zn,\qquad |t|<c,\quad 0\le i,j\le2.
$$

It rearranges to $a(t-2z-i)=b(t+3z+j)$. Euclid's divisibility lemma and $\gcd(a,b)=1$ give an integer $p$ with $t-2z-i=bp$ and $t+3z+j=ap$. Set $u=z-qp$. Subtraction and substitution give

$$
rp=5u+i+j,\qquad t=cp+2u+i.
$$

Since $0\le i+j\le4$, the first equality gives $u=\lfloor rp/5\rfloor$. If $p>0$, then $u\ge0$ and $t\ge c$. If $p<0$, then $u\le-1$, so $2u+i\le0$ and $t\le-c$. Both contradict $|t|<c$. If $p=0$, the first equality forces $u=i=j=0$, and then $z=t=0$. Thus only the trivial relation is possible, regardless of the sign of $q$.

Distinct candidate residues cannot collide: their index difference would give a nontrivial relation with $i=j=0$. A positive forbidden difference between two centers in any periods would give a relation with $i+j>0$. Negative differences are handled by reversing the centers. Hence $A_0$ is $M$-avoiding with exactly $c$ occupied residue classes modulo $n$. Each residue class has count within one of $(2N+1)/n$ on $[-N,N]$, so the symmetric density limit is $c/n$.

### Step 8. Remaining constructions and conclusion

For $r=3,4$, exchange $a,b$ and use Step 7 with $q'=-q-1$, $r'=5-r\in\{1,2\}$. The unchanged forbidden set admits a center set of density

$$
\frac{a+2q'}{2b+3a}=\frac{a-2(q+1)}{3a+2b}.
$$

For $r=0$, Step 2 supplied $5\mathbb Z$. Every branch now has a matching upper bound and a center set attaining it, proving the claim. $\square$

## Corrections or Missing Assumptions

None for the stated $k=m=2$ theorem. The temporary order assumption in Steps 3–6 is justified by symmetry; it is not an additional theorem assumption. Coprimality is used for the zero-remainder construction and Step 7, not for the path inequality or its equality condition.

## Open Risks

No unresolved mathematical step remains in this proof. Publication priority is not established or claimed. This document neither resolves the general $k,m$ conjecture nor certifies a complete machine formalization. Supporting finite computations have only the scope stated in their own recorded results.

This work was developed with AI assistance. Bibliographic attribution and source-license information are recorded in `REFERENCES.md`.
