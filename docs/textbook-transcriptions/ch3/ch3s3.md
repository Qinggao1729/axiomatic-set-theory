# Chapter 3 Section 3 (n-Ary Relations)

Source: Enderton, *Elements of Set Theory*, pp. 41-42.

**page 41**

## n-ARY RELATIONS

We can extend the ideas behind ordered pairs to the case of ordered triples and, more generally, to ordered $n$-tuples. For triples we define

$$\langle x, y, z \rangle = \langle\langle x, y \rangle, z \rangle.$$

**page 42**

Similarly we can form ordered quadruples:

$$\langle x_1, x_2, x_3, x_4 \rangle = \langle\langle x_1, x_2, x_3 \rangle, x_4 \rangle$$
$$= \langle\langle\langle x_1, x_2 \rangle, x_3 \rangle, x_4 \rangle.$$

Clearly we could continue in this way to define ordered quintuples or ordered $n$-tuples for any particular $n$. It is convenient for reasons of uniformity to define also the 1-tuple $\langle x \rangle = x$.

We define an *$n$-ary relation on $A$* to be a set of ordered $n$-tuples with all components in $A$. Thus a binary (2-ary) relation on $A$ is just a subset of $A \times A$. And a ternary (3-ary) relation on $A$ is a subset of $(A \times A) \times A$. There is, however, a terminological quirk here. If $n > 1$, then any $n$-ary relation on $A$ is actually a relation. But a unary (1-ary) relation on $A$ is just a subset of $A$; thus it may not be a relation at all.

## Exercise

**10.** Show that an ordered 4-tuple is also an ordered $m$-tuple for every positive integer $m$ less than 4.
