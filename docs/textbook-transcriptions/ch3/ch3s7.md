# Chapter 3 Section 7 (Ordering Relations)

Source: Enderton, *Elements of Set Theory*, pp. 62-64.

**page 62**

## ORDERING RELATIONS

The first example of a relation we gave in this chapter was the ordering relation

$$\{\langle 2, 3\rangle, \langle 2, 5\rangle, \langle 3, 5\rangle\}$$

on the set $\{2, 3, 5\}$; recall Fig. 7. Now we want to consider ordering relations on other sets. In the present section we will set forth the basic concepts, which will be useful in Chapter 5. A more thorough discussion of ordering relations can be found in Chapter 7.

Our first need is for a definition. What, in general, should it mean to say that $R$ is an ordering relation on a set $A$? Well, for one thing $R$ should tell us, given any distinct $x$ and $y$ in $A$, just which one is smaller. No $x$ should be smaller than itself. And furthermore if $x$ is less than $y$ and $y$ is less than $z$, then $x$ should be less than $z$. The following definition captures these ideas.

**Definition** Let $A$ be any set. A *linear ordering* on $A$ (also called a *total ordering* on $A$) is a binary relation $R$ on $A$ (i.e., $R \subseteq A \times A$) meeting the following two conditions:

(a) $R$ is a transitive relation; i.e., whenever $xRy$ and $yRz$, then $xRz$.

(b) $R$ satisfies trichotomy on $A$, by which we mean that for any $x$ and $y$ in $A$ exactly one of the three alternatives

$$xRy, \qquad x = y, \qquad yRx$$

holds.

**page 63**

To clarify the meaning of trichotomy, consider first the special case where $x$ and $y$ are the *same* member of $A$ (with two names). Then trichotomy demands that exactly one of

$$xRx, \qquad x = x, \qquad xRx$$

holds. Since the middle alternative certainly holds, we can conclude that $xRx$ *never* holds.

Next consider the case where $x$ and $y$ are two distinct members of $A$. Then the middle alternative $x = y$ fails, so trichotomy demands that either $xRy$ or $yRx$ (but not both). Thus we have proved the following:

**Theorem 3R** Let $R$ be a linear ordering on $A$.

(i) There is no $x$ for which $xRx$.

(ii) For distinct $x$ and $y$ in $A$, either $xRy$ or $yRx$.

In fact for a transitive relation $R$ on $A$, conditions (i) and (ii) are equivalent to trichotomy. A relation meeting condition (i) is called *irreflexive*; one meeting condition (ii) is said to be *connected* on $A$.

Note also that a linear ordering $R$ can never lead us in circles, e.g., there cannot exist a circle such as

$$x_1 R x_2, \qquad x_2 R x_3, \qquad x_3 R x_4, \qquad x_4 R x_5, \qquad x_5 R x_1.$$

This is because if we had such a circle, then by transitivity $x_1 R x_1$, contradicting part (i) of the foregoing theorem.

Of course "$R$" is not our favorite symbol for a linear ordering; our favorite is "$<$." For then we can write "$x < y$" to mean that the pair $\langle x, y\rangle$ is a member of the set $<$.

If $<$ is a linear ordering on $A$ and if $A$ is not too large, then we can draw a picture of the ordering. We represent the members of $A$ by dots, placing the dot for $x$ below the dot for $y$ whenever $x < y$. Then we add vertical lines to connect the dots. The resulting picture has the points of $A$ stretched out along a line, in the correct order. (The adjective "linear" reflects the possibility of drawing this picture.)

Figure 15 contains three such pictures. Part (a) is the picture for the usual order on $\{2, 3, 5\}$. Parts (b) and (c) portray the usual order on the natural numbers and on the integers, respectively. (Infinite pictures are more difficult to draw than finite pictures.)

In addition to the concept of linear ordering, there is the more general concept of a partial ordering. Partial orderings are discussed in the first section of Chapter 7. In fact you might want to read that section next, before going on to Chapter 4. At least look at Figs. 43 and 44 there, which contrast with Fig. 15.

**page 64**

**Fig. 15.** Linear orderings look linear.

## Exercises

**43.** Assume that $R$ is a linear ordering on a set $A$. Show that $R^{-1}$ is also a linear ordering on $A$.

**44.** Assume that $<$ is a linear ordering on a set $A$. Assume that $f : A \to A$ and that $f$ has the property that whenever $x < y$, then $f(x) < f(y)$. Show that $f$ is one-to-one and that whenever $f(x) < f(y)$, then $x < y$.

**45.** Assume that $<_A$ and $<_B$ are linear orderings on $A$ and $B$, respectively. Define the binary relation $<_L$ on the Cartesian product $A \times B$ by:

$$\langle a_1, b_1\rangle <_L \langle a_2, b_2\rangle \quad \text{iff} \quad \text{either } a_1 <_A a_2 \text{ or } (a_1 = a_2 \ \&\ b_1 <_B b_2)$$

Show that $<_L$ is a linear ordering on $A \times B$. (The relation $<_L$ is called *lexicographic* ordering, being the ordering used in making dictionaries.)

## Review Exercises

**46.** Evaluate the following sets:

(a) $\bigcap\bigcap\langle x, y\rangle$.

(b) $\bigcap\bigcap\bigcap\{\langle x, y\rangle\}^{-1}$.

**47.** (a) Find all of the functions from $\{0, 1, 2\}$ into $\{3, 4\}$.

(b) Find all of the functions from $\{0, 1, 2\}$ *onto* $\{3, 4, 5\}$.
