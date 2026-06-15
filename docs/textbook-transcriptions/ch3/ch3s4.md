# Chapter 3 Section 4 (Functions)

Source: Enderton, *Elements of Set Theory*, pp. 42-54.

**page 42**

## FUNCTIONS

Calculus books often describe a function as a rule that assigns to each object in a certain set (its domain) a unique object in a possibly different set (its range). A typical example is the squaring function, which assigns to each real number $x$ its square $x^2$. The action of this function on a particular number can be described by writing

$$3 \mapsto 9, \quad -2 \mapsto 4, \quad 1 \mapsto 1, \quad \tfrac{1}{2} \mapsto \tfrac{1}{4}, \quad \text{etc.}$$

Each individual action can be represented by an ordered pair:

$$\langle 3, 9 \rangle, \quad \langle -2, 4 \rangle, \quad \langle 1, 1 \rangle, \quad \langle \tfrac{1}{2}, \tfrac{1}{4} \rangle, \quad \text{etc.}$$

The set of all these pairs (one for each real number) adequately represents the squaring function. The set of pairs has at times been called the *graph* of the function; it is a subset of the coordinate plane $\mathbb{R} \times \mathbb{R}$. But the simplest procedure is to take this set of ordered pairs to *be* the function.

Thus a function is a set of ordered pairs (i.e., a relation). But it has a special property: It is "single-valued," i.e., for each $x$ in its domain there is a unique $y$ such that $x \mapsto y$. We build these ideas into the following definition.

**Definition** A *function* is a relation $F$ such that for each $x$ in dom $F$ there is only one $y$ such that $xFy$.

**page 43**

For a function $F$ and a point $x$ in dom $F$, the unique $y$ such that $xFy$ is called the *value* of $F$ at $x$ and is denoted $F(x)$. Thus $\langle x, F(x) \rangle \in F$. The "$F(x)$" notation was introduced by Euler in the 1700s. We hereby resolve to use this notation *only* when $F$ is a function and $x \in \text{dom } F$. There are, however, some artificial ways of defining $F(x)$ that are meaningful for any $F$ and $x$. For example, the set

$$\bigcup\{y \mid \langle x, y \rangle \in F\}$$

is equal to $F(x)$ whenever $F$ is a function and $x \in \text{dom } F$.

Functions are basic objects appearing in all parts of mathematics.¹ As a result, there is a good deal of terminology used in connection with functions. Unfortunately, no terminology has become uniformly standardized. We collect below some of this terminology.

We say that $F$ is a function *from $A$ into $B$* or that $F$ *maps $A$ into $B$* (written $F: A \to B$) iff $F$ is a function, dom $F = A$, and ran $F \subseteq B$. Note the unequal treatment of $A$ and $B$ here; we demand only that ran $F \subseteq B$. If, in addition, ran $F = B$, then $F$ is a function *from $A$ onto $B$*. (Thus any function $F$ maps its domain onto its range. And it maps its domain into any set $B$ that includes ran $F$. The applicability of the word "onto" depends both on $F$ and on the set $B$, not just on $F$. The word "onto" must never be used as an adjective.)

A function $F$ is *one-to-one* iff for each $y \in \text{ran } F$ there is only one $x$ such that $xFy$. For example, the function defined by

$$f(x) = x^3 \qquad \text{for each real number } x$$

is one-to-one, whereas the squaring function is not, since $(-3)^2 = 3^2$. One-to-one functions are sometimes called *injections*.

It will occasionally be useful to apply the concept of "one-to-one" to relations that are not functions. Since the phrase "one-to-one" seems inappropriate in such cases, we will use the phrase "single-rooted," in analogy to "single-valued."

**Definition** A set $R$ is *single-rooted* iff for each $y \in \text{ran } R$ there is only one $x$ such that $xRy$.

Thus for a function, it is single-rooted iff it is one-to-one.

It is entirely possible to have the domain of a function $F$ consist of ordered pairs or $n$-tuples. For example, addition is a function $+: \mathbb{R} \times \mathbb{R} \to \mathbb{R}$. Thus the domain of addition consists of pairs of numbers, and the addition function itself consists of triples of numbers. In place of $+(\langle x, y \rangle)$ we write either $+(x, y)$ or $x + y$.

**page 44**

The following operations are most commonly applied to functions, sometimes are applied to relations, but can actually be defined for arbitrary sets $A$, $F$, and $G$.

**Definition** (a) The *inverse* of $F$ is the set

$$F^{-1} = \{\langle u, v \rangle \mid vFu\}.$$

(b) The *composition* of $F$ and $G$ is the set

$$F \circ G = \{\langle u, v \rangle \mid \exists t (uGt\ \&\ tFv)\}.$$

(c) The *restriction* of $F$ to $A$ is the set

$$F \restriction A = \{\langle u, v \rangle \mid uFv\ \&\ u \in A\}.$$

(d) The *image* of $A$ under $F$ is the set

$$F[\![A]\!] = \text{ran}(F \restriction A)$$
$$= \{v \mid (\exists u \in A) uFv\}.$$

$F[\![A]\!]$ can be characterized more simply when $F$ is a function and $A \subseteq \text{dom } F$; in this case

$$F[\![A]\!] = \{F(u) \mid u \in A\}.$$

In each case we can easily apply a subset axiom to establish the existence of the desired set. Specifically, $F^{-1} \subseteq \text{ran } F \times \text{dom } F$, $F \circ G \subseteq \text{dom } G \times \text{ran } F$, $F \restriction A \subseteq F$, and $F[\![A]\!] \subseteq \text{ran } F$. (A more detailed justification of the definition of $F^{-1}$ would go as follows: By a subset axiom there is a set $B$ such that for any $x$,

$$x \in B \quad \Leftrightarrow \quad x \in \text{ran } F \times \text{dom } F\ \&\ \exists u\ \exists v(x = \langle u, v \rangle\ \&\ vFu).$$

It then follows that

$$x \in B \quad \Leftrightarrow \quad \exists u\ \exists v(x = \langle u, v \rangle\ \&\ vFu).$$

This unique set $B$ we denote as $F^{-1}$.)

*Example* Let $F: \mathbb{R} \to \mathbb{R}$ be defined by the equation $F(x) = x^2$. Let $A$ be the set $\{x \in \mathbb{R} \mid -1 \leq x \leq 2\}$, i.e., the closed interval $[-1, 2]$. Then $F[\![A]\!] = [0, 4]$; see Fig. 9. And $F^{-1}[\![A]\!] = [-\sqrt{2}, \sqrt{2}]$. Notice that although $F$ here is a function, $F^{-1}$ is *not* a function, because both $\langle 9, 3 \rangle$ and $\langle 9, -3 \rangle$ are in $F^{-1}$. The so-called "multiple-valued functions" are relations, not functions. People write "$F^{-1}(9) = \pm 3$," but it would be preferable to write: $F^{-1}[\![\{9\}]\!] = \{-3, 3\}$.

**page 45**

*Fig. 9.* $F[\![A]\!]$ is the image of the set $A$ under $F$.

*Example* In mathematical analysis it is often necessary to consider the "inverse image" of a set $A$ under a function $F$, i.e., the set $F^{-1}[\![A]\!]$. For a function $F$,

$$F^{-1}[\![A]\!] = \{x \in \text{dom } F \mid F(x) \in A\}$$

(Exercise 24). In general, $F^{-1}$ will not be a function.

*Example* Let $g$ be the sine function of trigonometry. Then $g^{-1}$ is not a function. (Why not?) But the restriction of $g$ to the closed interval $[-\pi/2, \pi/2]$ is one-to-one, and its inverse

$$(g \restriction [-\pi/2, \pi/2])^{-1}$$

is the arc sine function.

*Example* Assume that we have the set of all people (!) in mind, and we define $P$ to be the relation of parenthood, i.e.,

$$P = \{\langle x, y \rangle \mid x \text{ is a parent of } y\}.$$

Then

$$P^{-1} = \{\langle x, y \rangle \mid x \text{ is a son or daughter of } y\}$$

and

$$P \circ P = \{\langle x, y \rangle \mid x \text{ is a grandparent of } y\}.$$

If $A$ is the set of people born in Poland, then

$$(P \circ P)[\![A]\!] = \{t \mid \text{a grandparent of } t \text{ was born in Poland}\}.$$

**page 46**

To further complicate matters, let $S$ be the relation that holds between siblings:

$$S = \{\langle x, y \rangle \mid x \text{ is a brother or sister of } y\}$$

Then $S^{-1} = S$. To find out what $P \circ S$ is, we can calculate:

$$\langle x, y \rangle \in P \circ S \quad \Leftrightarrow \quad xSt\ \&\ tPy \quad \text{for some } t$$
$$\Leftrightarrow \quad x \text{ is a sibling of a parent of } y$$
$$\Leftrightarrow \quad x \text{ is an aunt or uncle of } y.$$

None of the relations in this example are functions.

*Example* Let

$$F = \{\langle \varnothing, a \rangle, \langle \{\varnothing\}, b \rangle\}.$$

Observe that $F$ is a function. We have

$$F^{-1} = \{\langle a, \varnothing \rangle, \langle b, \{\varnothing\} \rangle\}.$$

$F^{-1}$ is a function iff $a \neq b$. The restriction of $F$ to $\varnothing$ is $\varnothing$, but

$$F \restriction \{\varnothing\} = \{\langle \varnothing, a \rangle\}.$$

Consequently, $F[\![\{\varnothing\}]\!] = \{a\}$, in contrast to the fact that $F(\{\varnothing\}) = b$.

The following facts about inverses are not difficult to show; the proofs of some of them are left as exercises.

**Theorem 3E** For a set $F$, dom $F^{-1} = \text{ran } F$ and ran $F^{-1} = \text{dom } F$. For a relation $F$, $(F^{-1})^{-1} = F$.

**Theorem 3F** For a set $F$, $F^{-1}$ is a function iff $F$ is single-rooted. A relation $F$ is a function iff $F^{-1}$ is single-rooted.

**Theorem 3G** Assume that $F$ is a one-to-one function. If $x \in \text{dom } F$, then $F^{-1}(F(x)) = x$. If $y \in \text{ran } F$, then $F(F^{-1}(y)) = y$.

*Proof* Suppose that $x \in \text{dom } F$; then $\langle x, F(x) \rangle \in F$ and $\langle F(x), x \rangle \in F^{-1}$. Thus $F(x) \in \text{dom } F^{-1}$. $F^{-1}$ is a function by Theorem 3F, so $x = F^{-1}(F(x))$.

If $y \in \text{ran } F$, then by applying the first part of the theorem to $F^{-1}$ we obtain the equation $(F^{-1})^{-1}(F^{-1}(y)) = y$. But $(F^{-1})^{-1} = F$. $\dashv$

In place of Theorem 3G, we could have *defined* $F^{-1}$ (for a one-to-one function $F$) to be that function whose value at $F(x)$ is $x$ (and whose domain is ran $F$). But this would be too restrictive; $F^{-1}$ can be a useful relation even when it is not a function. Hence we prefer a definition of $F^{-1}$ that is applicable to any set.

**page 47**

**Theorem 3H** Assume that $F$ and $G$ are functions. Then $F \circ G$ is a function, its domain is

$$\{x \in \text{dom } G \mid G(x) \in \text{dom } F\},$$

and for $x$ in its domain, $(F \circ G)(x) = F(G(x))$.

*Proof* To see that $F \circ G$ is a function, assume that $x(F \circ G)y$ and $x(F \circ G)y'$. Then for some $t$ and $t'$,

$$xGt\ \&\ tFy \qquad \text{and} \qquad xGt'\ \&\ t'Fy'.$$

Since $G$ is a function, $t = t'$. Since $F$ is a function, $y = y'$. Hence $F \circ G$ is a function.

Now suppose that $x \in \text{dom } G$ and $G(x) \in \text{dom } F$. We must show that $x \in \text{dom}(F \circ G)$ and that $(F \circ G)(x) = F(G(x))$. We have $\langle x, G(x) \rangle \in G$ and $\langle G(x), F(G(x)) \rangle \in F$. Hence $\langle x, F(G(x)) \rangle \in F \circ G$, and this yields the desired facts.

Conversely, if $x \in \text{dom } F \circ G$, then we know that for some $y$ and $t$, $xGt$ and $tFy$. Hence $x \in \text{dom } G$ and $t = G(x) \in \text{dom } F$. $\dashv$

Again we could have *defined* $F \circ G$ (for functions $F$ and $G$) as the function with the properties stated in the above theorem. But we prefer to use a definition applicable to nonfunctions as well. For example, in Exercise 32, we will want $R \circ R$ for an arbitrary relation $R$.

*Example* Assume that $G$ is some one-to-one function. Then by Theorem 3H, $G^{-1} \circ G$ is a function, its domain is

$$\{x \in \text{dom } G \mid G(x) \in \text{dom } G^{-1}\} = \text{dom } G,$$

and for $x$ in its domain,

$$(G^{-1} \circ G)(x) = G^{-1}(G(x))$$
$$= x \qquad \text{by Theorem 3G.}$$

Thus $G^{-1} \circ G$ is $I_{\text{dom } G}$, the identity function on dom $G$, by Exercise 11. Similarly one can show that $G \circ G^{-1}$ is $I_{\text{ran } G}$ (Exercise 25).

**Theorem 3I** For any sets $F$ and $G$,

$$(F \circ G)^{-1} = G^{-1} \circ F^{-1}.$$

*Proof* Both $(F \circ G)^{-1}$ and $G^{-1} \circ F^{-1}$ are relations. We calculate:

$$\langle x, y \rangle \in (F \circ G)^{-1} \quad \Leftrightarrow \quad \langle y, x \rangle \in F \circ G$$
$$\Leftrightarrow \quad yGt\ \&\ tFx \qquad \text{for some } t$$
$$\Leftrightarrow \quad xF^{-1}t\ \&\ tG^{-1}y \qquad \text{for some } t$$
$$\Leftrightarrow \quad \langle x, y \rangle \in G^{-1} \circ F^{-1}.$$

$\dashv$

**page 48**

In a less abstract form, Theorem 3I expresses common knowledge. In getting dressed, one first puts on socks and then shoes. But in the inverse process of getting undressed, one first removes shoes and then socks.

**Theorem 3J** Assume that $F: A \to B$, and that $A$ is nonempty.

(a) There exists a function $G: B \to A$ (a "left inverse") such that $G \circ F$ is the identity function $I_A$ on $A$ iff $F$ is one-to-one.

(b) There exists a function $H: B \to A$ (a "right inverse") such that $F \circ H$ is the identity function $I_B$ on $B$ iff $F$ maps $A$ onto $B$.

*Proof* (a) First assume that there is a function $G$ for which $G \circ F = I_A$. If $F(x) = F(y)$, then by applying $G$ to both sides of the equation we have

$$x = G(F(x)) = G(F(y)) = y,$$

and hence $F$ is one-to-one.

For the converse, assume that $F$ is one-to-one. Then $F^{-1}$ is a function from ran $F$ onto $A$ (by Theorems 3E and 3F). The idea is to extend $F^{-1}$ to a function $G$ defined on all of $B$. By assumption $A$ is nonempty, so we can fix some $a$ in $A$. Then we define $G$ so that it assigns $a$ to every point in $B - \text{ran } F$:

$$G(x) = \begin{cases} F^{-1}(x) & \text{if } x \in \text{ran } F \\ a & \text{if } x \in B - \text{ran } F. \end{cases}$$

In one line,

$$G = F^{-1} \cup (B - \text{ran } F) \times \{a\}$$

(see Fig. 10a). This choice for $G$ does what we want: $G$ is a function mapping $B$ into $A$, dom$(G \circ F) = A$, and $G(F(x)) = F^{-1}(F(x)) = x$ for each $x$ in $A$. Hence $G \circ F = I_A$.

(b) Next assume that there is a function $H$ for which $F \circ H = I_B$. Then for any $y$ in $B$ we have $y = F(H(y))$, so that $y \in \text{ran } F$. Thus ran $F$ is all of $B$.

The converse poses a difficulty. We cannot take $H = F^{-1}$, because in general $F$ will not be one-to-one and so $F^{-1}$ will not be a function. Assume that $F$ maps $A$ onto $B$, so that ran $F = B$. The idea is that for each $y \in B$ we must *choose* some $x$ for which $F(x) = y$ and then let $H(y)$ be the chosen $x$. Since $y \in \text{ran } F$ we know that such $x$'s exist, so there is no problem (see Fig. 10b).

Or is there? For any *one* $y$ we know there exists an appropriate $x$. But that is not by itself enough to let us form a function $H$. We have in general no way of defining any one particular choice of $x$. What is needed here is the axiom of choice.

**page 49**

*Fig. 10.* The proof of Theorem 3J. In part (a), make $G(x) = a$ for $x \in B - \text{ran } F$. In part (b), $H(y)$ is the chosen $x$ for which $F(x) = y$.

**Axiom of Choice** (first form) For any relation $R$ there is a function $H \subseteq R$ with dom $H = \text{dom } R$.

With this axiom we can now proceed with the proof of Theorem 3J(b); take $H$ to be a function with $H \subseteq F^{-1}$ and dom $H = \text{dom } F^{-1} = \text{ran } F = B$. Then $H$ does what we want: Given any $y$ in $B$, we have $\langle y, H(y) \rangle \in F^{-1}$; hence $\langle H(y), y \rangle \in F$, and so $F(H(y)) = y$. $\dashv$

In Chapter 6 we will give a systematic discussion of the axiom of choice. It is the only axiom that we discuss without using the marginal stripe.

**page 50**

**Theorem 3K** The following hold for any sets. ($F$ need not be a function.)

(a) The image of a union is the union of the images:

$$F[\![A \cup B]\!] = F[\![A]\!] \cup F[\![B]\!] \qquad \text{and} \qquad F[\![\textstyle\bigcup \mathscr{A}]\!] = \bigcup\{F[\![A]\!] \mid A \in \mathscr{A}\}.$$

(b) The image of an intersection is included in the intersection of the images:

$$F[\![A \cap B]\!] \subseteq F[\![A]\!] \cap F[\![B]\!] \qquad \text{and} \qquad F[\![\textstyle\bigcap \mathscr{A}]\!] \subseteq \bigcap\{F[\![A]\!] \mid A \in \mathscr{A}\}$$

for nonempty $\mathscr{A}$. Equality holds if $F$ is single-rooted.

(c) The image of a difference includes the difference of the images:

$$F[\![A]\!] - F[\![B]\!] \subseteq F[\![A - B]\!].$$

Equality holds if $F$ is single-rooted.

*Example* Let $F: \mathbb{R} \to \mathbb{R}$ be defined by $F(x) = x^2$. Let $A$ and $B$ be the closed intervals $[-2, 0]$ and $[1, 2]$:

$$A = \{x \mid -2 \leq x \leq 0\} \qquad \text{and} \qquad B = \{x \mid 1 \leq x \leq 2\}.$$

Then $F[\![A]\!] = [0, 4]$ and $F[\![B]\!] = [1, 4]$. This example shows that equality does not always hold in parts (b) and (c) of Theorem 3K, for $F[\![A \cap B]\!] = F[\![\varnothing]\!] = \varnothing$, whereas $F[\![A]\!] \cap F[\![B]\!] = [1, 4]$. And $F[\![A]\!] - F[\![B]\!] = [0, 1)$, whereas $F[\![A - B]\!] = F[\![A]\!] = [0, 4]$.

*Proof* To prove Theorem 3K we calculate

$$y \in F[\![A \cup B]\!] \quad \Leftrightarrow \quad (\exists x \in A \cup B) xFy$$
$$\Leftrightarrow \quad (\exists x \in A) xFy \text{ or } (\exists x \in B) xFy$$
$$\Leftrightarrow \quad y \in F[\![A]\!] \text{ or } y \in F[\![B]\!].$$

This proves the first half of (a). For intersections we have the corresponding calculation, except that the middle step

$$(\exists x \in A \cap B) xFy \quad \Rightarrow \quad (\exists x \in A) xFy\ \&\ (\exists x \in B) xFy$$

is not always reversible. It is possible that both $x_1 \in A$ with $x_1 Fy$ and $x_2 \in B$ with $x_2 Fy$, and yet there might be no $x$ in $A \cap B$ with $xFy$. But if $F$ is single-rooted, then $x_1 = x_2$ and so it is in $A \cap B$. Thus we obtain the first half of (b).

The second halves of (a) and (b) generalize the first halves. The proofs follow the same outlines as the first halves, but we leave the details to Exercise 26.

**page 51**

For part (c) we also calculate:

$$y \in F[\![A]\!] - F[\![B]\!] \quad \Leftrightarrow \quad (\exists x \in A) xFy\ \&\ \neg (\exists t \in B) tFy$$
$$\Rightarrow \quad (\exists x \in A - B) xFy$$
$$\Leftrightarrow \quad y \in F[\![A - B]\!].$$

Again if $F$ is single-rooted, then there is only one $x$ such that $xFy$. In this case the middle step can be reversed. $\dashv$

Since the inverse of a function is always single-rooted, we have as an immediate consequence of Theorem 3K that unions, intersections, and relative complements are always preserved under inverse images.

**Corollary 3L** For any function $G$ and sets $A$, $B$, and $\mathscr{A}$:

$$G^{-1}[\![\textstyle\bigcup \mathscr{A}]\!] = \bigcup\{G^{-1}[\![A]\!] \mid A \in \mathscr{A}\},$$
$$G^{-1}[\![\textstyle\bigcap \mathscr{A}]\!] = \bigcap\{G^{-1}[\![A]\!] \mid A \in \mathscr{A}\} \qquad \text{for } \mathscr{A} \neq \varnothing,$$
$$G^{-1}[\![A - B]\!] = G^{-1}[\![A]\!] - G^{-1}[\![B]\!].$$

We conclude our discussion of functions with some definitions that may be useful later. Our intent is to build a large working vocabulary of set-theoretic notations.

An infinite union is often "indexed," as when we write $\bigcup_{i \in I} A_i$. We can give a formal definition to such a union as follows. Let $I$ be a set, called the *index* set. Let $F$ be a function whose domain includes $I$. Then we define

$$\bigcup_{i \in I} F(i) = \bigcup\{F(i) \mid i \in I\}$$
$$= \{x \mid x \in F(i) \text{ for some } i \text{ in } I\}.$$

For example, if $I = \{0, 1, 2, 3\}$, then

$$\bigcup_{i \in I} F(i) = \bigcup\{F(0), F(1), F(2), F(3)\}$$
$$= F(0) \cup F(1) \cup F(2) \cup F(3).$$

Similar remarks apply to intersections (provided that $I$ is nonempty):

$$\bigcap_{i \in I} F(i) = \bigcap\{F(i) \mid i \in I\}$$
$$= \{x \mid x \in F(i) \text{ for every } i \text{ in } I\}.$$

If we use the alternative notation

$$F_i = F(i),$$

**page 52**

then we can rewrite the above equations as

$$\bigcup_{i \in I} F_i = \bigcup\{F_i \mid i \in I\}$$
$$= \{x \mid x \in F_i \text{ for some } i \text{ in } I\}$$

and

$$\bigcap_{i \in I} F_i = \bigcap\{F_i \mid i \in I\}$$
$$= \{x \mid x \in F_i \text{ for every } i \text{ in } I\}.$$

For sets $A$ and $B$ we can form the collection of functions $F$ from $A$ into $B$. Call the set of all such functions $^A B$:

$$^A B = \{F \mid F \text{ is a function from } A \text{ into } B\}.$$

If $F: A \to B$, then $F \subseteq A \times B$, and so $F \in \mathscr{P}(A \times B)$. Consequently we can apply a subset axiom to $\mathscr{P}(A \times B)$ to construct the set of all functions from $A$ into $B$.

The notation $^A B$ is read "$B$-pre-$A$." Some authors write $B^A$ instead; this notation is derived from the fact that if $A$ and $B$ are finite sets and the number of elements in $A$ and $B$ is $a$ and $b$, respectively, then $^A B$ has $b^a$ members. (To see this, note that for each of the $a$ elements of $A$, we can choose among $b$ points in $B$ into which it could be mapped. The number of ways of making all $a$ such choices is $b \cdot b \cdots b$, $a$ times.) We will return to this point in Chapter 6.

*Example* Let $\omega = \{0, 1, 2, \ldots\}$. Then $^\omega \{0, 1\}$ is the set of all possible functions $f: \omega \to \{0, 1\}$. Such an $f$ can be thought of as an infinite sequence $f(0), f(1), f(2), \ldots$ of 0's and 1's.

*Example* For a nonempty set $A$, we have $^A \varnothing = \varnothing$. This is because no function could have a nonempty domain and an empty range. On the other hand, $^\varnothing A = \{\varnothing\}$ for any set $A$, because $\varnothing: \varnothing \to A$, but $\varnothing$ is the only function with empty domain. As a special case, we have $^\varnothing \varnothing = \{\varnothing\}$.

---

¹ Despite this ubiquity, the general concept of "a function" emerged slowly over a period of time. There was a reluctance to separate the concept of a function itself from the idea of a written formula defining the function. There still is.

## Exercises

**11.** Prove the following version (for functions) of the extensionality principle: Assume that $F$ and $G$ are functions, dom $F = \text{dom } G$, and $F(x) = G(x)$ for all $x$ in the common domain. Then $F = G$.

**12.** Assume that $f$ and $g$ are functions and show that

$$f \subseteq g \quad \Leftrightarrow \quad \text{dom } f \subseteq \text{dom } g\ \&\ (\forall x \in \text{dom } f) f(x) = g(x).$$

**page 53**

**13.** Assume that $f$ and $g$ are functions with $f \subseteq g$ and dom $g \subseteq \text{dom } f$. Show that $f = g$.

**14.** Assume that $f$ and $g$ are functions.
   (a) Show that $f \cap g$ is a function.
   (b) Show that $f \cup g$ is a function iff $f(x) = g(x)$ for every $x$ in $(\text{dom } f) \cap (\text{dom } g)$.

**15.** Let $\mathscr{A}$ be a set of functions such that for any $f$ and $g$ in $\mathscr{A}$, either $f \subseteq g$ or $g \subseteq f$. Show that $\bigcup \mathscr{A}$ is a function.

**16.** Show that there is no set to which every function belongs.

**17.** Show that the composition of two single-rooted sets is again single-rooted. Conclude that the composition of two one-to-one functions is again one-to-one.

**18.** Let $R$ be the set

$$\{\langle 0, 1 \rangle, \langle 0, 2 \rangle, \langle 0, 3 \rangle, \langle 1, 2 \rangle, \langle 1, 3 \rangle, \langle 2, 3 \rangle\}.$$

Evaluate the following: $R \circ R$, $R \restriction \{1\}$, $R^{-1} \restriction \{1\}$, $R[\![\{1\}]\!]$, and $R^{-1}[\![\{1\}]\!]$.

**19.** Let

$$A = \{\langle \varnothing, \{\varnothing, \{\varnothing\}\} \rangle, \langle \{\varnothing\}, \varnothing \rangle\}.$$

Evaluate each of the following: $A(\varnothing)$, $A[\![\varnothing]\!]$, $A[\![\{\varnothing\}]\!]$, $A[\![\{\varnothing, \{\varnothing\}\}]\!]$, $A^{-1}$, $A \circ A$, $A \restriction \varnothing$, $A \restriction \{\varnothing\}$, $A \restriction \{\varnothing, \{\varnothing\}\}$, $\bigcup\bigcup A$.

**20.** Show that $F \restriction A = F \cap (A \times \text{ran } F)$.

**21.** Show that $(R \circ S) \circ T = R \circ (S \circ T)$ for any sets $R$, $S$, and $T$.

**22.** Show that the following are correct for any sets.
   (a) $A \subseteq B \Rightarrow F[\![A]\!] \subseteq F[\![B]\!]$.
   (b) $(F \circ G)[\![A]\!] = F[\![G[\![A]\!]]\!]$.
   (c) $Q \restriction (A \cup B) = (Q \restriction A) \cup (Q \restriction B)$.

**23.** Let $I_A$ be the identity function on the set $A$. Show that for any sets $B$ and $C$,

$$B \circ I_A = B \restriction A \qquad \text{and} \qquad I_A[\![C]\!] = A \cap C.$$

**24.** Show that for a function $F$, $F^{-1}[\![A]\!] = \{x \in \text{dom } F \mid F(x) \in A\}$.

**25.** (a) Assume that $G$ is a one-to-one function. Show that $G \circ G^{-1}$ is $I_{\text{ran } G}$, the identity function on ran $G$.
   (b) Show that the result of part (a) holds for any function $G$, not necessarily one-to-one.

**26.** Prove the second halves of parts (a) and (b) of Theorem 3K.

**27.** Show that dom$(F \circ G) = G^{-1}[\![\text{dom } F]\!]$ for any sets $F$ and $G$. ($F$ and $G$ need not be functions.)

**page 54**

**28.** Assume that $f$ is a one-to-one function from $A$ into $B$, and that $G$ is the function with dom $G = \mathscr{P}A$ defined by the equation $G(X) = f[\![X]\!]$. Show that $G$ maps $\mathscr{P}A$ one-to-one into $\mathscr{P}B$.

**29.** Assume that $f: A \to B$ and define a function $G: B \to \mathscr{P}A$ by

$$G(b) = \{x \in A \mid f(x) = b\}.$$

Show that if $f$ maps $A$ onto $B$, then $G$ is one-to-one. Does the converse hold?

**30.** Assume that $F: \mathscr{P}A \to \mathscr{P}A$ and that $F$ has the monotonicity property:

$$X \subseteq Y \subseteq A \quad \Rightarrow \quad F(X) \subseteq F(Y).$$

Define

$$B = \bigcap\{X \subseteq A \mid F(X) \subseteq X\} \qquad \text{and} \qquad C = \bigcup\{X \subseteq A \mid X \subseteq F(X)\}.$$

   (a) Show that $F(B) = B$ and $F(C) = C$.
   (b) Show that if $F(X) = X$, then $B \subseteq X \subseteq C$.
