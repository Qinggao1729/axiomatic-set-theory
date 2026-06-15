# Chapter 2 Section 2 (Arbitrary Unions and Intersections)

Source: Enderton, *Elements of Set Theory*, pp. 23-26.

**page 23**

## ARBITRARY UNIONS AND INTERSECTIONS

The union operation previously described allows us to form the union $a \cup b$ of two sets. By repeating the operation, we can form the union of three sets or the union of forty sets. But suppose we want the union of infinitely many sets; suppose we have an infinite collection of sets

$$A = \{b_0, b_1, b_2, \ldots\}$$

and we want to take the union of all the $b_i$'s. For this we need a more general union operation:

$$\bigcup A = \bigcup_i b_i$$
$$= \{x \mid x \text{ belongs to some member } b_i \text{ of } A\}.$$

This leads us to make the following definition. For any set $A$, the *union* $\bigcup A$ of $A$ is the set defined by

$$\bigcup A = \{x \mid x \text{ belongs to some member of } A\}$$
$$= \{x \mid (\exists b \in A)\ x \in b\}.$$

**page 24**

Thus $\bigcup A$ is a melting pot into which all members of $A$ are dumped. For example, suppose $Un$ is (as on p. 4) the set of countries belonging to the United Nations. Then $\bigcup Un$ is the set of all people that are citizens of some country belonging to the United Nations. A smaller example (and one that avoids sets of people) is

$$\bigcup\{\{2, 4, 6\}, \{6, 16, 26\}, \{0\}\}.$$

You should evaluate this expression to make certain that you understand the union operation. If you do it correctly, you will end up with a set of six numbers.

We need an improved version of the union axiom in order to know that a set exists containing the members of the members of $A$.

**Union Axiom** For any set $A$, there exists a set $B$ whose elements are exactly the members of the members of $A$:

$$\forall x[x \in B \iff (\exists b \in A)\ x \in b].$$

We can state the definition of $\bigcup A$ in the following form:

$$x \in \bigcup A \iff (\exists b \in A)\ x \in b.$$

For example,

$$\bigcup\{a, b\} = \{x \mid x \text{ belongs to some member of } \{a, b\}\}$$
$$= \{x \mid x \text{ belongs to } a \text{ or to } b\}$$
$$= a \cup b.$$

This example shows that our preliminary form of the union axiom can be discarded in favor of the new form. That is, the set $a \cup b$ produced by the preliminary form can also be obtained from pairing and the revised form of the union axiom.

Similarly we have

$$\bigcup\{a, b, c, d\} = a \cup b \cup c \cup d \quad \text{and} \quad \bigcup\{a\} = a.$$

An extreme case is $\bigcup\varnothing = \varnothing$.

We also want a corresponding generalization of the intersection operation. Suppose we want to take the intersection of infinitely many sets $b_0, b_1, \ldots$. Then where

$$A = \{b_0, b_1, \ldots\}$$

the desired intersection can be informally characterized as

$$\bigcap A = \bigcap_i b_i$$
$$= \{x \mid x \text{ belongs to every } b_i \text{ in } A\}.$$

**page 25**

In general, we define for every nonempty set $A$, the *intersection* $\bigcap A$ of $A$ by the condition

$$x \in \bigcap A \iff x \text{ belongs to every member of } A.$$

In contrast to the union operation, no special axiom is needed to justify the intersection operation. Instead we have the following theorem.

**Theorem 2B** For any nonempty set $A$, there exists a unique set $B$ such that for any $x$,

$$x \in B \iff x \text{ belongs to every member of } A.$$

This theorem permits defining $\bigcap A$ to be that unique set $B$.

*Proof* We are given that $A$ is nonempty; let $c$ be some fixed member of $A$. Then by a subset axiom there is a set $B$ such that for any $x$,

$$x \in B \iff x \in c\ \&\ x \text{ belongs to every other member of } A$$
$$\iff x \text{ belongs to every member of } A.$$

Uniqueness, as always, follows from extensionality. $\dashv$

*Examples*

$$\bigcap\{\{1, 2, 8\}, \{2, 8\}, \{4, 8\}\} = \{8\},$$
$$\bigcup\{\{1, 2, 8\}, \{2, 8\}, \{4, 8\}\} = \{1, 2, 4, 8\}.$$

*Examples*

$$\bigcap\{a\} = a,$$
$$\bigcap\{a, b\} = a \cap b,$$
$$\bigcap\{a, b, c\} = a \cap b \cap c.$$

In these last examples, as $A$ becomes larger, $\bigcap A$ gets smaller. More precisely: Whenever $A \subseteq B$, then $\bigcap B \subseteq \bigcap A$. There is one troublesome extreme case. What happens if $A = \varnothing$? For any $x$ at all, it is vacuously true that $x$ belongs to every member of $\varnothing$. (There can be no member of $\varnothing$ to which $x$ fails to belong.) Thus it looks as if $\bigcap\varnothing$ should be the class $\mathbf{V}$ of all sets. By Theorem 2A, there is no set $C$ such that for all $x$,

$$x \in C \iff x \text{ belongs to every member of } \varnothing$$

since the right side is true of every $x$. This presents a mild notational problem: How do we define $\bigcap\varnothing$? The situation is analogous to division by zero in arithmetic. How does one define $a \div 0$? One option is to leave $\bigcap\varnothing$ undefined, since there is no very satisfactory way of defining it. This option works perfectly well, but some logicians dislike it. It leaves $\bigcap\varnothing$ as an untidy loose end, which they may later trip over. The other option is to select some arbitrary scapegoat (the set $\varnothing$ is always used for this) and define $\bigcap\varnothing$ to equal that object. Either way, whenever one forms $\bigcap A$ one must beware the possibility that perhaps $A = \varnothing$. Since it makes no difference which of the two options one follows, we will not bother to make a choice between them at all.

**page 26**

*Example* If $b \in A$, then $b \subseteq \bigcup A$.

*Example* If $\{\{x\}, \{x, y\}\} \in A$, then $\{x, y\} \in \bigcup A$, $x \in \bigcup\bigcup A$, and $y \in \bigcup\bigcup A$.

*Example* $\bigcap\{\{a\}, \{a, b\}\} = \{a\} \cap \{a, b\} = \{a\}$. Hence

$$\bigcup\bigcap\{\{a\}, \{a, b\}\} = \bigcup\{a\} = a.$$

On the other hand,

$$\bigcap\bigcup\{\{a\}, \{a, b\}\} = \bigcap\{a, b\} = a \cap b.$$

## Exercises

See also the Review Exercises at the end of this chapter.

**1.** Assume that $A$ is the set of integers divisible by 4. Similarly assume that $B$ and $C$ are the sets of integers divisible by 9 and 10, respectively. What is in $A \cap B \cap C$?

**2.** Give an example of sets $A$ and $B$ for which $\bigcup A = \bigcup B$ but $A \neq B$.

**3.** Show that every member of a set $A$ is a subset of $\bigcup A$. (This was stated as an example in this section.)

**4.** Show that if $A \subseteq B$, then $\bigcup A \subseteq \bigcup B$.

**5.** Assume that every member of $\mathscr{A}$ is a subset of $B$. Show that $\bigcup\mathscr{A} \subseteq B$.

**6.** (a) Show that for any set $A$, $\bigcup\mathscr{P}A = A$.
(b) Show that $A \subseteq \mathscr{P}\bigcup A$. Under what conditions does equality hold?

**7.** (a) Show that for any sets $A$ and $B$,

$$\mathscr{P}A \cap \mathscr{P}B = \mathscr{P}(A \cap B).$$

(b) Show that $\mathscr{P}A \cup \mathscr{P}B \subseteq \mathscr{P}(A \cup B)$. Under what conditions does equality hold?

**8.** Show that there is no set to which every singleton (that is, every set of the form $\{x\}$) belongs. [*Suggestion*: Show that from such a set, we could construct a set to which every set belonged.]

**9.** Give an example of sets $a$ and $B$ for which $a \in B$ but $\mathscr{P}a \notin \mathscr{P}B$.

**10.** Show that if $a \in B$, then $\mathscr{P}a \in \mathscr{P}\mathscr{P}\bigcup B$. [*Suggestion*: If you need help, look in the Appendix.]
