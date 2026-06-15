# Chapter 3 Section 2 (Relations)

Source: Enderton, *Elements of Set Theory*, pp. 39-41.

**page 39**

## RELATIONS

Before attempting to say what, in general, a relation is, it would be prudent to contemplate a few examples.

The ordering relation $<$ on the set $\{2, 3, 5\}$, is one example. We might say that $<$ relates each number to each of the larger numbers. Thus $3 < 5$, so $<$ relates 3 to 5. Pictorially we can represent this by drawing an arrow from 3 to 5. Altogether we get three arrows in this way (Fig. 7).

*Fig. 7.* The ordering relation $<$ on $\{2, 3, 5\}$.

What *set* adequately encodes this ordering relation? In place of the arrows, we take the ordered pairs $\langle 2, 3 \rangle$, $\langle 2, 5 \rangle$, and $\langle 3, 5 \rangle$. The set of these pairs

$$R = \{\langle 2, 3 \rangle, \langle 2, 5 \rangle, \langle 3, 5 \rangle\}$$

completely captures the information in Fig. 7. At one time it was fashionable to refer to the set $R$ as the *graph* of the relation, a terminology that seems particularly appropriate if we think of $R$ as a subset of the coordinate plane. But nowadays an even simpler viewpoint has become dominant: $R$ *is* the ordering relation on $\{2, 3, 5\}$. It consists of the pairs tying each number to the larger numbers; a relation *is* this collection of "ties."

A homier example might be the relation of marriage. (We ignore for the moment the fact that we banished people from our set theory.) This relation is the aggregate total of individual ties between each married person and his or her spouse. Or to say it more mathematically, the relation is

$$\{\langle x, y \rangle \mid x \text{ is married to } y\}.$$

**page 40**

You have probably guessed that for us a relation will be a set of ordered pairs. And there will be no further restrictions; *any* set of ordered pairs is some relation, even if a peculiar one.

**Definition** A *relation* is a set of ordered pairs.

For a relation $R$, we sometimes write $xRy$ in place of $\langle x, y \rangle \in R$. For example, in the case of the ordering relation $<$ on the set $\mathbb{R}$ of real numbers

$$< = \{\langle x, y \rangle \in \mathbb{R} \times \mathbb{R} \mid x \text{ is less than } y\},$$

the notation "$x < y$" is preferred to "$\langle x, y \rangle \in <$."

*Examples* Let $\omega$ be the set $\{0, 1, 2, \ldots\}$, which is introduced more formally in the next chapter. Then the divisibility relation is

$$\{\langle m, n \rangle \in \omega \times \omega \mid (\exists p \in \omega) m \cdot p = n\}.$$

The identity relation on $\omega$ is

$$I_\omega = \{\langle n, n \rangle \mid n \in \omega\}.$$

And *any* subset of $\omega \times \omega$ (of which there are a great many) is some sort of relation.

Of course some relations are much more interesting than others. In the coming pages we shall look at functions, equivalence relations, and ordering relations. At this point we make some very general definitions.

**Definition** We define the *domain* of $R$ (dom $R$), the *range* of $R$ (ran $R$), and the *field* of $R$ (fld $R$) by

$$x \in \text{dom } R \quad \Leftrightarrow \quad \exists y\ \langle x, y \rangle \in R,$$
$$x \in \text{ran } R \quad \Leftrightarrow \quad \exists t\ \langle t, x \rangle \in R,$$
$$\text{fld } R \quad = \quad \text{dom } R \cup \text{ran } R.$$

For example, let $\mathbb{R}$ be the set of all real numbers (a set we construct officially in Chapter 5) and suppose that $R \subseteq \mathbb{R} \times \mathbb{R}$. Then $R$ is a subset of the coordinate plane (Fig. 8). The projection of $R$ onto the horizontal axis is dom $R$, and the projection onto the vertical axis is ran $R$.

To justify the foregoing definition, we must be sure that for any given $R$, there exists a set containing all first coordinates and second coordinates of pairs of $R$. The problem here is analogous to the recent problem of justifying the definition of $A \times B$, which was accomplished by Corollary 3C. The crucial fact needed now is that there exists a large set already containing all of the elements we seek. This fact is provided by the following lemma, which is related to Lemma 3B. (Lemma 3D was stated as an example in the preceding chapter.)

**page 41**

**Lemma 3D** If $\langle x, y \rangle \in A$, then $x$ and $y$ belong to $\bigcup\bigcup A$.

*Proof* We assume that $\{\{x\}, \{x, y\}\} \in A$. Consequently, $\{x, y\} \in \bigcup A$ since it belongs to a member of $A$. And from this we conclude that $x \in \bigcup\bigcup A$ and $y \in \bigcup\bigcup A$. $\dashv$

This lemma indicates how we can use subset axioms to construct the domain and range of $R$:

$$\text{dom } R = \{x \in \textstyle\bigcup\bigcup R \mid \exists y\ \langle x, y \rangle \in R\},$$
$$\text{ran } R = \{x \in \textstyle\bigcup\bigcup R \mid \exists t\ \langle t, x \rangle \in R\}.$$

*Fig. 8.* A relation as a subset of the plane.

## Exercises

**6.** Show that a set $A$ is a relation iff $A \subseteq \text{dom } A \times \text{ran } A$.

**7.** Show that if $R$ is a relation, then fld $R = \bigcup\bigcup R$.

**8.** Show that for any set $\mathscr{A}$:

$$\text{dom } \bigcup \mathscr{A} = \bigcup\{\text{dom } R \mid R \in \mathscr{A}\},$$
$$\text{ran } \bigcup \mathscr{A} = \bigcup\{\text{ran } R \mid R \in \mathscr{A}\}.$$

**9.** Discuss the result of replacing the union operation by the intersection operation in the preceding problem.
