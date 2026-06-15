# Chapter 3 Section 6 (Equivalence Relations)

Source: Enderton, *Elements of Set Theory*, pp. 55-62.

**page 55**

## EQUIVALENCE RELATIONS

Consider a set $A$ (Fig. 12a). We might want to partition $A$ into little boxes (Fig. 12b). For example, take $A=\omega$; we can partition $\omega$ into six parts:

$$
\{0, 6, 12, \ldots\},
$$
$$
\{1, 7, 13, \ldots\},
$$
$$
\vdots
$$
$$
\{5, 11, 17, \ldots\}.
$$

By "partition" we mean that every element of $A$ is in exactly one little box, and that each box is a nonempty subset of $A$.

Now we need some mental agility. We want to think of each little box as being a single object, instead of thinking of it as a plurality of objects. (Actually we have been doing this sort of thing throughout the book, whenever we think of a set as a single object. It is really no harder than thinking of a brick house as a single object and not as a multitude of bricks.) This changes the picture (Fig. 12c); each box is now, in our mind, a single point. The set $B$ of boxes is very different from the set $A$. In our example, $B$ has only six members whereas $A$ is infinite. (When we get around to defining "six" and "infinite" officially, we must certainly do it in a way that makes the preceding sentence true.)

**page 56**

The process of transforming a situation like Fig. 12a into Fig. 12c is common in abstract algebra and elsewhere in mathematics. And in Chapter 5 the process will be applied several times in the construction of the real numbers.

Suppose we now define a binary relation $R$ on $A$ as follows: For $x$ and $y$ in $A$,

$$
xRy \iff x \text{ and } y \text{ are in the same little box.}
$$

Then we can easily see that $R$ has the following three properties.

1. $R$ is *reflexive on* $A$, by which we mean that $xRx$ for all $x\in A$.
2. $R$ is *symmetric*, by which we mean that whenever $xRy$, then also $yRx$.
3. $R$ is *transitive*, by which we mean that whenever $xRy$ and $yRz$, then also $xRz$.

**Definition** $R$ is an *equivalence relation on* $A$ iff $R$ is a binary relation on $A$ that is reflexive on $A$, symmetric, and transitive.

**Theorem 3M** If $R$ is a symmetric and transitive relation, then $R$ is an equivalence relation on $\operatorname{fld}\,R$.

*Proof* Any relation $R$ is a binary relation on its field, since

$$
R \subseteq \operatorname{dom}R \times \operatorname{ran}R \subseteq \operatorname{fld}R \times \operatorname{fld}R.
$$

What we must show is that $R$ is reflexive on $\operatorname{fld}R$. We have

$$
x\in\operatorname{dom}R \Rightarrow xRy \text{ for some } y
$$
$$
\Rightarrow xRy \ \&\ yRx \text{ by symmetry}
$$
$$
\Rightarrow xRx \text{ by transitivity},
$$

and a similar calculation applies to points in $\operatorname{ran}R$.

**page 57**

This theorem deserves a precautionary note: If $R$ is a symmetric and transitive relation on $A$, it does not follow that $R$ is an equivalence relation on $A$. $R$ is reflexive on $\operatorname{fld}R$, but $\operatorname{fld}R$ may be a small subset of $A$.

We have shown how a partition of a set $A$ induces an equivalence relation. (A more formal version of this is in Exercise 37.) Next we want to reverse the process, and show that from any equivalence relation $R$ on $A$, we get a partition of $A$.

**Definition** The set $[x]_R$ is defined by

$$
[x]_R=\{t\mid xRt\}.
$$

If $R$ is an equivalence relation and $x\in\operatorname{fld}R$, then $[x]_R$ is called the *equivalence class* of $x$ (modulo $R$). If the relation $R$ is fixed by the context, we may write just $[x]$.

The status of $[x]_R$ as a set is guaranteed by a subset axiom, since $[x]_R\subseteq \operatorname{ran}R$. Furthermore we can construct a set of equivalence classes such as $\{[x]_R\mid x\in A\}$, since this set is included in $\mathcal{P}(\operatorname{ran}R)$.

**Lemma 3N** Assume that $R$ is an equivalence relation on $A$ and that $x$ and $y$ belong to $A$. Then

$$
[x]_R=[y]_R \iff xRy.
$$

*Proof* $(\Rightarrow)$ Assume that $[x]_R=[y]_R$. We know that $y\in[y]_R$ (because $yRy$), consequently $y\in[x]_R$ (because $[x]_R=[y]_R$). By the definition of $[x]_R$, this means that $xRy$.

$(\Leftarrow)$ Next assume that $xRy$. Then

$$
t\in[y]_R \Rightarrow yRt
$$
$$
\Rightarrow xRt \text{ because } xRy \text{ and } R \text{ is transitive}
$$
$$
\Rightarrow t\in[x]_R.
$$

Thus $[y]_R\subseteq [x]_R$. Since $R$ is symmetric, we also have $yRx$ and we can reverse $x$ and $y$ in the above argument to obtain $[x]_R\subseteq [y]_R$. $\dashv$

**Definition** A *partition* $\Pi$ of a set $A$ is a set of nonempty subsets of $A$ that is disjoint and exhaustive, i.e.,

(a) no two different sets in $\Pi$ have any common elements, and  
(b) each element of $A$ is in some set in $\Pi$.

**Theorem 3P** Assume that $R$ is an equivalence relation on $A$. Then the set $\{[x]_R\mid x\in A\}$ of all equivalence classes is a partition of $A$.

*Proof* Each equivalence class $[x]_R$ is nonempty (because $x\in[x]_R$) and is a subset of $A$ (because $R$ is a binary relation on $A$). The main thing that we must prove is that the collection of equivalence classes is disjoint, i.e., part (a) of the above definition is satisfied. So suppose that $[x]_R$ and $[y]_R$ have a common element $t$. Thus

**page 58**

$$
xRt \text{ and } yRt.
$$

But then $xRy$ and by Lemma 3N, $[x]_R=[y]_R$. $\dashv$

If $R$ is an equivalence relation on $A$, then we can define the *quotient set*

$$
A/R=\{[x]_R\mid x\in A\}
$$

whose members are the equivalence classes. (The expression $A/R$ is read "A modulo $R$.") We also have the *natural map* (or *canonical map*) $\varphi:A\to A/R$ defined by

$$
\varphi(x)=[x]_R
$$

for $x\in A$.

**Example** Let $\omega=\{0,1,2,\ldots\}$; define the binary relation $\sim$ on $\omega$ by

$$
m\sim n \iff m-n \text{ is divisible by } 6.
$$

Then $\sim$ is an equivalence relation on $\omega$ (as you should verify). The quotient set $\omega/\sim$ has six members:

$$
[0],\ [1],\ [2],\ [3],\ [4],\ [5],
$$

corresponding to the six possible remainders after division by 6.

**Example** The relation of congruence of triangles in the plane is an equivalence relation.

**Example** Textbooks on linear algebra often define vectors in the plane as follows. Let $A$ be the set of all directed line segments in the plane. Two such line segments are considered to be equivalent iff they have the same length and direction. A vector is then defined to be an equivalence class of directed line segments. But to avoid the necessity of dealing explicitly with equivalence relations, books use phrases like "equivalent vectors are regarded as equal even though they are located in different positions," or "we write $PQ=RS$ to say that $PQ$ and $RS$ have the same length and direction even though they are not identical sets of points," or simply "we identify two line segments having the same length and direction."

**Example** Let $F:A\to B$ and for points in $A$ define

$$
x\sim y \iff F(x)=F(y).
$$

The relation $\sim$ is an equivalence relation on $A$. There is a unique one-to-one function $\hat{F}:A/\sim\to B$ such that $F=\hat{F}\circ\varphi$ (where $\varphi$ is the natural map as shown in Fig. 13). The value of $\hat{F}$ at a particular equivalence class is the common value of $F$ at the members of the equivalence class.

**page 59**

The last problem we want to examine in this section is the problem of defining functions on a quotient set. Specifically, assume that $R$ is an equivalence relation on $A$ and that $F:A\to A$. We ask whether or not there exists a corresponding function $\hat{F}:A/R\to A/R$ such that for all $x\in A$,

$$
\hat{F}([x]_R)=[F(x)]_R
$$

(see Fig. 14). Here we are attempting to define the value of $\hat{F}$ at an equivalence class by selecting a particular member $x$ from the class and then forming $[F(x)]_R$. But suppose $x_1$ and $x_2$ are in the same equivalence class. Then $\hat{F}$ is not well defined unless $F(x_1)$ and $F(x_2)$ are in the same equivalence class.

**page 60**

**Example** Consider $\omega/\sim$ where $m\sim n$ iff $m-n$ is divisible by 6. Three functions from $\omega$ into $\omega$ are defined by

$$
F_1(n)=2n,\qquad F_2(n)=n^2,\qquad F_3(n)=2^n.
$$

In each case we can ask whether there is $\hat{F}_i:\omega/\sim\to\omega/\sim$ such that for every $n$ in $\omega$:

$$
\hat{F}_1([n])=[2n],\qquad \hat{F}_2([n])=[n^2],\qquad \hat{F}_3([n])=[2^n].
$$

It is easy to see that if $m\sim n$, then $2m\sim 2n$. Because of this fact $\hat{F}_1$ is well defined; that is, there exists a function $\hat{F}_1$ satisfying the equation $\hat{F}_1([n])=[2n]$. No matter what representative $m$ of the equivalence class $[n]$ we look at, we always obtain the same equivalence class $[2m]$. (For further details, see the proof of Theorem 3Q below.) Similarly if $m\sim n$, then $m^2\sim n^2$, for recall that $m^2-n^2=(m+n)(m-n)$. Consequently $\hat{F}_2$ is also well defined. On the other hand, $\hat{F}_3$ is not well defined. For example, $0\sim 6$ but $2^0=1\not\sim 64=2^6$. Thus although $[0]=[6]$, we have $[2^0]\neq [2^6]$. Hence there cannot possibly exist any function $\hat{F}_3$ such that the equation $\hat{F}_3([n])=[2^n]$ holds for both $n=0$ and $n=6$.

In order to formulate a general theorem here, let us say that $F$ is *compatible* with $R$ iff for all $x$ and $y$ in $A$,

$$
xRy \Rightarrow F(x)RF(y).
$$

**Theorem 3Q** Assume that $R$ is an equivalence relation on $A$ and that $F:A\to A$. If $F$ is compatible with $R$, then there exists a unique $\hat{F}:A/R\to A/R$ such that

$$
(\star)\qquad \hat{F}([x]_R)=[F(x)]_R \qquad \text{for all } x\in A.
$$

If $F$ is not compatible with $R$, then no such $\hat{F}$ exists. Analogous results apply to functions from $A\times A$ into $A$.

*Proof* First assume that $F$ is not compatible; we will show that there can be no $\hat{F}$ satisfying $(\star)$. The incompatibility tells us that for certain $x$ and $y$ in $A$ we have $xRy$ (and hence $[x]=[y]$) but not $F(x)RF(y)$ (and hence $[F(x)]\neq [F(y)]$). For $(\star)$ to hold we would need both

$$
\hat{F}([x])=[F(x)] \quad \text{and} \quad \hat{F}([y])=[F(y)].
$$

But this is impossible, since the left sides coincide and the right sides differ.

Now for the converse, assume that $F$ is compatible with $R$. Since $(\star)$ demands that the pair $\langle [x],[F(x)]\rangle \in \hat{F}$, we will try defining $\hat{F}$ to be the set of all such ordered pairs:

$$
\hat{F}=\{\langle [x],[F(x)]\rangle\mid x\in A\}.
$$

**page 61**

The crucial matter is whether this relation $\hat{F}$ is a function. So consider pairs $\langle [x],[F(x)]\rangle$ and $\langle [y],[F(y)]\rangle$ in $\hat{F}$. The calculation

$$
[x]=[y] \Rightarrow xRy \quad \text{by Lemma 3N}
$$
$$
\Rightarrow F(x)RF(y) \quad \text{by compatibility}
$$
$$
\Rightarrow [F(x)]=[F(y)] \quad \text{by Lemma 3N}
$$

shows that $\hat{F}$ is indeed a function. The remaining things to check are easier. Clearly $\operatorname{dom}\hat{F}=A/R$ and $\operatorname{ran}\hat{F}\subseteq A/R$, hence $\hat{F}:A/R\to A/R$. Finally $(\star)$ holds because $\langle [x],[F(x)]\rangle\in\hat{F}$.

We leave it to you to explain why $\hat{F}$ is unique, and to formulate the "analogous results" for a binary operation (Exercise 42). $\dashv$

## Exercises

**32.**  
(a) Show that $R$ is symmetric iff $R^{-1}\subseteq R$.  
(b) Show that $R$ is transitive iff $R\circ R\subseteq R$.

**33.** Show that $R$ is a symmetric and transitive relation iff $R=R^{-1}\circ R$.

**34.** Assume that $\mathcal{A}$ is a nonempty set, every member of which is a transitive relation.  
(a) Is the set $\bigcap\mathcal{A}$ a transitive relation?  
(b) Is $\bigcup\mathcal{A}$ a transitive relation?

**35.** Show that for any $R$ and $x$, we have $[x]_R=R[\{x\}]$.

**36.** Assume that $f:A\to B$ and that $R$ is an equivalence relation on $B$. Define $Q$ to be the set

$$
\{\langle x,y\rangle\in A\times A\mid \langle f(x),f(y)\rangle\in R\}.
$$

Show that $Q$ is an equivalence relation on $A$.

**37.** Assume that $\Pi$ is a partition of a set $A$. Define the relation $R_\Pi$ as follows:

$$
xR_\Pi y \iff (\exists B\in\Pi)(x\in B \ \&\ y\in B).
$$

Show that $R_\Pi$ is an equivalence relation on $A$. (This is a formalized version of the discussion at the beginning of this section.)

**38.** Theorem 3P shows that $A/R$ is a partition of $A$ whenever $R$ is an equivalence relation on $A$. Show that if we start with the equivalence relation $R_\Pi$ of the preceding exercise, then the partition $A/R_\Pi$ is just $\Pi$.

**39.** Assume that we start with an equivalence relation $R$ on $A$ and define $\Pi$ to be the partition $A/R$. Show that $R_\Pi$, as defined in Exercise 37, is just $R$.

**page 62**

**40.** Define an equivalence relation $R$ on the set $P$ of positive integers by

$$
mR n \iff m \text{ and } n \text{ have the same number of prime factors.}
$$

Is there a function $f:P/R\to P/R$ such that $f([n]_R)=[3n]_R$ for each $n$?

**41.** Let $\mathbb{R}$ be the set of real numbers and define the relation $Q$ on $\mathbb{R}\times\mathbb{R}$ by $\langle u,v\rangle Q\langle x,y\rangle$ iff $u+y=x+v$.

(a) Show that $Q$ is an equivalence relation on $\mathbb{R}\times\mathbb{R}$.  
(b) Is there a function $G:(\mathbb{R}\times\mathbb{R})/Q\to(\mathbb{R}\times\mathbb{R})/Q$ satisfying the equation

$$
G([\langle x,y\rangle]_Q)=[\langle x+2y,\ y+2x\rangle]_Q\ ?
$$

**42.** State precisely the "analogous results" mentioned in Theorem 3Q. (This will require extending the concept of compatibility in a suitable way.)

