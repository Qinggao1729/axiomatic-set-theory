# Chapter 3 Section 5 (Infinite Cartesian Products)

Source: Enderton, *Elements of Set Theory*, pp. 54-55.

**page 54**

## INFINITE CARTESIAN PRODUCTS[^1]

We can form something like the Cartesian product of infinitely many sets, provided that the sets are suitably indexed. More specifically, let $I$ be a set (which we will refer to as the *index set*) and let $H$ be a function whose domain includes $I$. Then for each $i$ in $I$ we have the set $H(i)$; we want the product of the $H(i)$'s for all $i \in I$. We define:

$$
⨉_{i \in I} H(i) = \{f \mid f \text{ is a function with domain } I \text{ and } (\forall i \in I)\, f(i) \in H(i)\}.
$$

Thus the members of $⨉_{i \in I} H(i)$ are "$I$-tuples" (i.e., functions with domain $I$) for which the "$i$th coordinate" (i.e., the value at $i$) is in $H(i)$.

The members of $⨉_{i \in I} H(i)$ are all functions from $I$ into $\bigcup_{i \in I} H(i)$ and hence are members of ${}^{I}(\bigcup_{i \in I} H(i))$. Thus the set $⨉_{i \in I} H(i)$ can be formed by applying a subset axiom to ${}^{I}(\bigcup_{i \in I} H(i))$.

*Example* If for every $i \in I$ we have $H(i) = A$ for some one fixed $A$, then

$$
⨉_{i \in I} H(i) = {}^{I}A.
$$

*Example* Assume that the index set is the set $\omega = \{0, 1, 2, \ldots\}$. Then $⨉_{i \in \omega} H(i)$ consists of "$\omega$-sequences" (i.e., functions with domain $\omega$) that have for their $i$th term some member of $H(i)$. If we picture the sets $H(i)$ as shown in Fig. 11, then a typical member of $⨉_{i \in \omega} H(i)$ is a "thread" that selects a point from each set.

**page 55**

If any one $H(i)$ is empty, then clearly the product $⨉_{i \in I} H(i)$ is empty. Conversely, suppose that $H(i) \neq \varnothing$ for every $i$ in $I$. Does it follow that

$$
⨉_{i \in I} H(i) \neq \varnothing
$$

? To obtain a member $f$ of the product, we need to select some member from each $H(i)$, and put $f(i)$ equal to that selected member. This requires the axiom of choice, and in fact this is one of the many equivalent ways of stating the axiom.

**Axiom of Choice** (second form) For any set $I$ and any function $H$ with domain $I$, if $H(i) \neq \varnothing$ for all $i$ in $I$, then

$$
⨉_{i \in I} H(i) \neq \varnothing.
$$

*Fig. 11.* The thread is a member of the Cartesian product.

## Exercise

**31.** Show that from the first form of the axiom of choice we can prove the second form, and conversely.

[^1]: This section may be omitted if certain obvious adjustments are made in Theorem 6M.
