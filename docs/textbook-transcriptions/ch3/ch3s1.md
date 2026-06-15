# Chapter 3 Section 1 (Ordered Pairs)

Source: Enderton, *Elements of Set Theory*, pp. 35-39.

**page 35**

In this chapter we introduce some concepts that are important throughout mathematics. The correct formulation (and understanding) of the definitions will be a major goal. The theorems initially will be those needed to justify the definitions, and those verifying some properties of the defined objects.

## ORDERED PAIRS

The pair set $\{1, 2\}$ can be thought of as an unordered pair, since $\{1, 2\} = \{2, 1\}$. We will need another object $\langle 1, 2 \rangle$ that will encode more information: that 1 is the first component and 2 is the second. In particular, we will demand that $\langle 1, 2 \rangle \neq \langle 2, 1 \rangle$.

More generally, we want to define a set $\langle x, y \rangle$ that uniquely encodes both what $x$ and $y$ are, and also what order they are in. In other words, if an ordered pair can be represented in two ways

$$\langle x, y \rangle = \langle u, v \rangle,$$

then the representations are identical in the sense that $x = u$ and $y = v$. And in fact any way of defining $\langle x, y \rangle$ that satisfies this property of unique decomposition will suffice. It will be instructive to consider first some examples of definitions *lacking* this property.

**page 36**

*Example 1* If we define $\langle x, y \rangle_1 = \{x, y\}$, then (as noted above), $\langle 1, 2 \rangle_1 = \langle 2, 1 \rangle_1$.

*Example 2* Let $\langle x, y \rangle_2 = \{x, \{y\}\}$. Again the desired property fails, since $\langle \{\varnothing\}, \{\varnothing\} \rangle_2 = \langle \{\{\varnothing\}\}, \varnothing \rangle_2$, both sides being equal to $\{\{\varnothing\}, \{\{\varnothing\}\}\}$.

The first successful definition was given by Norbert Wiener in 1914, who proposed to let

$$\langle x, y \rangle_3 = \{\{\{x\}, \varnothing\}, \{\{y\}\}\}.$$

A simpler definition was given by Kazimierz Kuratowski in 1921, and is the definition in general use today:

**Definition** $\langle x, y \rangle$ is defined to be $\{\{x\}, \{x, y\}\}$.

We must prove that this definition succeeds in capturing the desired property: The ordered pair $\langle x, y \rangle$ uniquely determines both what $x$ and $y$ are, and the order upon them.

**Theorem 3A** $\langle u, v \rangle = \langle x, y \rangle$ iff $u = x$ and $v = y$.

*Proof* One direction is trivial; if $u = x$ and $v = y$, then $\langle u, v \rangle$ is the same thing as $\langle x, y \rangle$.

To prove the interesting direction, assume that $\langle u, v \rangle = \langle x, y \rangle$, i.e.,

$$\{\{u\}, \{u, v\}\} = \{\{x\}, \{x, y\}\}.$$

Then we have

$$\{u\} \in \{\{x\}, \{x, y\}\} \qquad \text{and} \qquad \{u, v\} \in \{\{x\}, \{x, y\}\}.$$

From the first of these, we know that either

$$\text{(a)}\quad \{u\} = \{x\} \qquad \text{or} \qquad \text{(b)}\quad \{u\} = \{x, y\},$$

and from the second we know that either

$$\text{(c)}\quad \{u, v\} = \{x\} \qquad \text{or} \qquad \text{(d)}\quad \{u, v\} = \{x, y\}.$$

First suppose (b) holds; then $u = x = y$. Then (c) and (d) are equivalent, and tell us that $u = v = x = y$. In this case the conclusion of the theorem holds. Similarly if (c) holds, we have the same situation.

There remains the case in which (a) and (d) hold. From (a) we have $u = x$. From (d) we get either $u = y$ or $v = y$. In the first case (b) holds; that case has already been considered. In the second case we have $v = y$, as desired. $\dashv$

**page 37**

The preceding theorem lets us unambiguously define the *first coordinate* of $\langle x, y \rangle$ to be $x$, and the *second coordinate* to be $y$.

*Example* Let $\mathbb{R}$ be the set of all real numbers. The pair $\langle x, y \rangle$ can be visualized as a point in the plane (Fig. 6), where coordinate axes have been established. This representation of points in the plane is attributed to Descartes.

Now suppose that we have two sets $A$ and $B$, and we form ordered pairs $\langle x, y \rangle$ with $x \in A$ and $y \in B$. The collection of *all* such pairs is called the *Cartesian product* $A \times B$ of $A$ and $B$:

$$A \times B = \{\langle x, y \rangle \mid x \in A\ \&\ y \in B\}.$$

*Fig. 6.* The pair $\langle x, y \rangle$ as a point in the plane.

We must verify that this collection is actually a set before the definition is legal. When we use the abstraction notation $\{t \mid \_\_ t \_\_\}$ for a set, we must verify that there does indeed exist a set $D$ such that

$$t \in D \quad \Leftrightarrow \quad \_\_ t \_\_$$

for every $t$. For example, just as strings of symbols, the expressions

$$\{x \mid x = x\} \qquad \text{and} \qquad \{x \mid x \neq x\}$$

look similar. But by Theorem 2A the first does not name a set, whereas (by the empty set axiom) the second does.

The strategy we follow in order to show that $A \times B$ is a set (and not a proper class) runs as follows. If we can find a large set that already contains all of the pairs $\langle x, y \rangle$ we want, then we can use a subset axiom to cut things down to $A \times B$. A suitable large set to start with is provided by the next lemma.

**Lemma 3B** If $x \in C$ and $y \in C$, then $\langle x, y \rangle \in \mathscr{P}\mathscr{P}C$.

*Proof* As the following calculation demonstrates, the fact that the braces in "$\{\{x\}, \{x, y\}\}$" are nested to a depth of 2 is responsible for the two applications of the power set operation:

**page 38**

$$x \in C \qquad \text{and} \qquad y \in C,$$
$$\{x\} \subseteq C \qquad \text{and} \qquad \{x, y\} \subseteq C,$$
$$\{x\} \in \mathscr{P}C \qquad \text{and} \qquad \{x, y\} \in \mathscr{P}C,$$
$$\{\{x\}, \{x, y\}\} \subseteq \mathscr{P}C,$$
$$\{\{x\}, \{x, y\}\} \in \mathscr{P}\mathscr{P}C.$$

$\dashv$

**Corollary 3C** For any sets $A$ and $B$, there is a set whose members are exactly the pairs $\langle x, y \rangle$ with $x \in A$ and $y \in B$.

*Proof* From a subset axiom we can construct

$$\{w \in \mathscr{P}\mathscr{P}(A \cup B) \mid w = \langle x, y \rangle \text{ for some } x \text{ in } A \text{ and some } y \text{ in } B\}.$$

Clearly this set contains only pairs of the desired sort; by the preceding lemma it contains them all. $\dashv$

This corollary justifies our earlier definition of the Cartesian product $A \times B$.

As you have probably observed, our decision to use the Kuratowski definition

$$\langle x, y \rangle = \{\{x\}, \{x, y\}\}$$

is somewhat arbitrary. There are other definitions that would serve as well. The essential fact is that satisfactory ways exist of defining ordered pairs in terms of other concepts of set theory.

## Exercises

See also the Review Exercises at the end of this chapter.

**1.** Suppose that we attempted to generalize the Kuratowski definitions of ordered pairs to ordered triples by defining

$$\langle x, y, z \rangle^* = \{\{x\}, \{x, y\}, \{x, y, z\}\}.$$

Show that this definition is unsuccessful by giving examples of objects $u, v, w, x, y, z$ with $\langle x, y, z \rangle^* = \langle u, v, w \rangle^*$ but with either $y \neq v$ or $z \neq w$ (or both).

**2.** (a) Show that $A \times (B \cup C) = (A \times B) \cup (A \times C)$.
   (b) Show that if $A \times B = A \times C$ and $A \neq \varnothing$, then $B = C$.

**3.** Show that $A \times \bigcup \mathscr{B} = \bigcup\{A \times X \mid X \in \mathscr{B}\}$.

**4.** Show that there is no set to which every ordered pair belongs.

**page 39**

**5.** (a) Assume that $A$ and $B$ are given sets, and show that there exists a set $C$ such that for any $y$,

$$y \in C \quad \Leftrightarrow \quad y = \{x\} \times B \text{ for some } x \text{ in } A.$$

In other words, show that $\{\{x\} \times B \mid x \in A\}$ is a set.
   (b) With $A$, $B$, and $C$ as above, show that $A \times B = \bigcup C$.
