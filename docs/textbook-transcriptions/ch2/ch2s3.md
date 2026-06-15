# Chapter 2 Section 3 (Algebra of Sets)

Source: Enderton, *Elements of Set Theory*, pp. 27-33.

**page 27**

## ALGEBRA OF SETS

Two basic operations on sets are the operations of union and intersection:

$$A \cup B = \{x \mid x \in A \text{ or } x \in B\},$$
$$A \cap B = \{x \mid x \in A\ \&\ x \in B\}.$$

Also we have for any sets $A$ and $B$ the *relative complement* $A - B$ of $B$ in $A$:

$$A - B = \{x \in A \mid x \notin B\}.$$

The usual diagram for $A - B$ is shown in Fig. 4. In some books the minus sign is needed for other uses, and the relative complement is then denoted $A \setminus B$.

*Fig. 4.* The shaded area represents $A - B$.

The union axiom was used to give us $A \cup B$. But $A \cap B$ and $A - B$ were both obtained from subset axioms.

We cannot form (as a set) the "absolute complement" of $B$, i.e., $\{x \mid x \notin B\}$. This class fails to be a set, for its union with $B$ would be the class of all sets. In any event, the absolute complement is unlikely to be an interesting object of study.

For example, suppose one is studying sets of real numbers. Let $\mathbb{R}$ be the set of all real numbers, and suppose that $B \subseteq \mathbb{R}$. Then the relative complement $\mathbb{R} - B$ consists of these real numbers not in $B$. On the other hand, the absolute complement of $B$ would be a huge class containing all manner of irrelevant things; it would contain *any* set that was not a real number.

*Example* Let $A$ be the set of all left-handed people, let $B$ be the set of all blond people, and let $C$ be the set of all male people. (We choose to suppress in this example, as in others, the fact that we officially banned people from our sets.) Then $A \cup (B - C)$ is the set of all people who either are left-handed or are blond nonmales (or both). On the other hand $(A \cup B) - C$ is the set of all nonmales who are either left-handed or blond. These two sets are different; Joe (who is a left-handed male) belongs to the first set but not the second. The set

$$(A - C) \cup (B - C)$$

is the same as one of the two sets mentioned above. Which one?

**page 28**

The study of the operations of union ($\cup$), intersection ($\cap$), and relative complementation ($-$), together with the inclusion relation ($\subseteq$), goes by the name of the *algebra of sets*. In some ways, the algebra of sets obeys laws reminiscent of the algebra of real numbers (with $+$, $\cdot$, $-$, and $\leq$), but there are significant differences.

The following identities, which hold for any sets, are some of the elementary facts of the algebra of sets.

*Commutative laws*

$$A \cup B = B \cup A \quad \text{and} \quad A \cap B = B \cap A.$$

*Associative laws*

$$A \cup (B \cup C) = (A \cup B) \cup C,$$
$$A \cap (B \cap C) = (A \cap B) \cap C.$$

*Distributive laws*

$$A \cap (B \cup C) = (A \cap B) \cup (A \cap C),$$
$$A \cup (B \cap C) = (A \cup B) \cap (A \cup C).$$

*De Morgan's laws*

$$C - (A \cup B) = (C - A) \cap (C - B),$$
$$C - (A \cap B) = (C - A) \cup (C - B).$$

*Identities involving $\varnothing$*

$$A \cup \varnothing = A \quad \text{and} \quad A \cap \varnothing = \varnothing,$$
$$A \cap (C - A) = \varnothing.$$

Often one considers sets, all of which are subsets of some large set or "space" $S$. A common example is the study of subsets of the space $\mathbb{R}$ of real numbers. Assume then that $A$ and $B$ are subsets of $S$. Then we can abbreviate $S - A$ as simply $-A$, the set $S$ being understood as fixed. In this abbreviation, De Morgan's laws become

$$-(A \cup B) = -A \cap -B,$$
$$-(A \cap B) = -A \cup -B.$$

**page 29**

Further, we have (still under the assumption that $A \subseteq S$)

$$A \cup S = S \quad \text{and} \quad A \cap S = A,$$
$$A \cup -A = S \quad \text{and} \quad A \cap -A = \varnothing.$$

Now we should say something about how one proves all these facts. Let us take as a sample the distributive law:

$$A \cap (B \cup C) = (A \cap B) \cup (A \cap C).$$

One way to check this is to draw the picture (Fig. 5). After shading the region representing $A \cap (B \cup C)$ and the region representing $(A \cap B) \cup (A \cap C)$, one discovers that these regions are the same.

*Fig. 5.* Diagram for three sets.

Is the foregoing proof, which relies on a picture, really trustworthy? Let us run through it again without the picture. To prove the desired equation, it suffices (by extensionality) to consider an arbitrary $x$, and to show that $x$ belongs to $A \cap (B \cup C)$ iff it belongs to $(A \cap B) \cup (A \cap C)$. So consider this arbitrary $x$. We do not know for sure whether $x \in A$ or not, whether $x \in B$ or not, etc., but we can list all eight possibilities:

| | | |
| --- | --- | --- |
| $x \in A$ | $x \in B$ | $x \in C$ |
| $x \in A$ | $x \in B$ | $x \notin C$ |
| $x \in A$ | $x \notin B$ | $x \in C$ |
| $x \in A$ | $x \notin B$ | $x \notin C$ |
| $x \notin A$ | $x \in B$ | $x \in C$ |
| $x \notin A$ | $x \in B$ | $x \notin C$ |
| $x \notin A$ | $x \notin B$ | $x \in C$ |
| $x \notin A$ | $x \notin B$ | $x \notin C$ |

**page 30**

(These cases correspond to the eight regions of Fig. 5.) We can then verify that in each of the eight cases,

$$x \in A \cap (B \cup C) \quad \text{iff} \quad x \in (A \cap B) \cup (A \cap C).$$

For example, in the fifth case we find that

$$x \notin A \cap (B \cup C) \quad \text{and} \quad x \notin (A \cap B) \cup (A \cap C).$$

(What region of Fig. 5 does this case represent?) When verification for the seven other cases has been made, the proof of the equation is complete.

This method of proof is applicable to all the equations listed thus far; in fact it works for any equation or inclusion of this sort. If the equation involves $n$ letters, then there will be $2^n$ cases. In the distributive law we had three letters and eight cases. But less mechanical methods of proof will be needed for some of the facts listed below.

For the inclusion relation, we have the following monotonicity properties:

$$A \subseteq B \implies A \cup C \subseteq B \cup C,$$
$$A \subseteq B \implies A \cap C \subseteq B \cap C,$$
$$A \subseteq B \implies \bigcup A \subseteq \bigcup B,$$

and the "antimonotone" results:

$$A \subseteq B \implies C - B \subseteq C - A,$$
$$\varnothing \neq A \subseteq B \implies \bigcap B \subseteq \bigcap A.$$

In each case, the proof is straightforward. For example, in the last case, we assume that every member of $A$ is also a member of $B$. Hence if $x \in \bigcap B$, i.e., if $x$ belongs to every member of $B$, then *a fortiori* $x$ belongs to every member of the smaller collection $A$. And consequently $x \in \bigcap A$.

Next we list some more identities involving arbitrary unions and intersections.

*Distributive laws*

$$A \cup \bigcap\mathscr{B} = \bigcap\{A \cup X \mid X \in \mathscr{B}\} \quad \text{for} \quad \mathscr{B} \neq \varnothing,$$
$$A \cap \bigcup\mathscr{B} = \bigcup\{A \cap X \mid X \in \mathscr{B}\}.$$

The notation used on the right side is an extension of the abstraction notation. The set $\{A \cup X \mid X \in \mathscr{B}\}$ (read "the set of all $A \cup X$ such that $X \in \mathscr{B}$") is the unique set $\mathscr{D}$ whose members are exactly the sets of the form $A \cup X$ for some $X$ in $\mathscr{B}$; i.e.,

$$t \in \mathscr{D} \iff t = A \cup X \quad \text{for some } X \text{ in } \mathscr{B}.$$

**page 31**

The existence of such a set $\mathscr{D}$ can be proved by observing that $A \cup X \subseteq A \cup \bigcup\mathscr{B}$. Hence the set $\mathscr{D}$ we seek is a subset of $\mathscr{P}(A \cup \bigcup\mathscr{B})$. A subset axiom produces

$$\{t \in \mathscr{P}(A \cup \bigcup\mathscr{B}) \mid t = A \cup X \text{ for some } X \text{ in } \mathscr{B}\},$$

and this is exactly the set $\mathscr{D}$.

For another example of this notation, suppose that sets $\mathscr{A}$ and $C$ are under consideration. Then

$$\{C - X \mid X \in \mathscr{A}\}$$

is the set of relative complements of members of $\mathscr{A}$, i.e., for any $t$,

$$t \in \{C - X \mid X \in \mathscr{A}\} \iff t = C - X \quad \text{for some } X \text{ in } \mathscr{A}.$$

Similarly, $\{\mathscr{P}X \mid X \in \mathscr{A}\}$ is the set for which

$$t \in \{\mathscr{P}X \mid X \in \mathscr{A}\} \iff t = \mathscr{P}X \quad \text{for some } X \text{ in } \mathscr{A}.$$

It is not entirely obvious that any such set can be proved to exist, but see Exercise 10.

*De Morgan's laws (for $\mathscr{A} \neq \varnothing$)*

$$C - \bigcup\mathscr{A} = \bigcap\{C - X \mid X \in \mathscr{A}\},$$
$$C - \bigcap\mathscr{A} = \bigcup\{C - X \mid X \in \mathscr{A}\}.$$

If $\bigcup\mathscr{A} \subseteq S$, then these laws can be written as

$$-\bigcup\mathscr{A} = \bigcap\{-X \mid X \in \mathscr{A}\},$$
$$-\bigcap\mathscr{A} = \bigcup\{-X \mid X \in \mathscr{A}\},$$

where it is understood that $-X$ is $S - X$.

To prove, for example, that for nonempty $\mathscr{A}$ the equation

$$C - \bigcup\mathscr{A} = \bigcap\{C - X \mid X \in \mathscr{A}\}$$

holds, we can argue as follows:

$$t \in C - \bigcup\mathscr{A} \implies t \in C \text{ but } t \text{ belongs to no member of } \mathscr{A}$$
$$\implies t \in C - X \quad \text{for every } X \text{ in } \mathscr{A}$$
$$\implies t \in \bigcap\{C - X \mid X \in \mathscr{A}\}.$$

Furthermore every step reverses, so that "$\Rightarrow$" can become "$\Leftrightarrow$." (A question for the alert reader: Where do we use the fact that $\mathscr{A} \neq \varnothing$?)

**page 32**

*A Final Remark on Notation* There is another style of writing some of the unions and intersections with which we have been working. We can write, for example,

$$\bigcap_{X \in \mathscr{B}} (A \cup X) \quad \text{for} \quad \bigcap\{A \cup X \mid X \in \mathscr{B}\}$$

and

$$\bigcup_{X \in \mathscr{A}} (C - X) \quad \text{for} \quad \bigcup\{C - X \mid X \in \mathscr{A}\}.$$

But for the most part we will stick to our original notation.

## Exercises

**11.** Show that for any sets $A$ and $B$,

$$A = (A \cap B) \cup (A - B) \quad \text{and} \quad A \cup (B - A) = A \cup B.$$

**12.** Verify the following identity (one of De Morgan's laws):

$$C - (A \cap B) = (C - A) \cup (C - B).$$

**13.** Show that if $A \subseteq B$, then $C - B \subseteq C - A$.

**14.** Show by example that for some sets $A$, $B$, and $C$, the set $A - (B - C)$ is different from $(A - B) - C$.

**15.** Define the symmetric difference $A + B$ of sets $A$ and $B$ to be the set $(A - B) \cup (B - A)$.
(a) Show that $A \cap (B + C) = (A \cap B) + (A \cap C)$.
(b) Show that $A + (B + C) = (A + B) + C$.

**16.** Simplify:

$$[(A \cup B \cup C) \cap (A \cup B)] - [(A \cup (B - C)) \cap A].$$

**17.** Show that the following four conditions are equivalent.
(a) $A \subseteq B$, (b) $A - B = \varnothing$,
(c) $A \cup B = B$, (d) $A \cap B = A$.

**18.** Assume that $A$ and $B$ are subsets of $S$. List all of the different sets that can be made from these three by use of the binary operations $\cup$, $\cap$, and $-$.

**19.** Is $\mathscr{P}(A - B)$ always equal to $\mathscr{P}A - \mathscr{P}B$? Is it ever equal to $\mathscr{P}A - \mathscr{P}B$?

**20.** Let $A$, $B$, and $C$ be sets such that $A \cup B = A \cup C$ and $A \cap B = A \cap C$. Show that $B = C$.

**21.** Show that $\bigcup(A \cup B) = \bigcup A \cup \bigcup B$.

**22.** Show that if $A$ and $B$ are nonempty sets, then $\bigcap(A \cup B) = \bigcap A \cap \bigcap B$.

**page 33**

**23.** Show that if $\mathscr{B}$ is nonempty, then $A \cup \bigcap\mathscr{B} = \bigcap\{A \cup X \mid X \in \mathscr{B}\}$.

**24.** (a) Show that if $\mathscr{A}$ is nonempty, then $\mathscr{P}\bigcap\mathscr{A} = \bigcap\{\mathscr{P}X \mid X \in \mathscr{A}\}$.
(b) Show that

$$\bigcup\{\mathscr{P}X \mid X \in \mathscr{A}\} \subseteq \mathscr{P}\bigcup\mathscr{A}.$$

Under what conditions does equality hold?

**25.** Is $A \cup \bigcup\mathscr{B}$ always the same as $\bigcup\{A \cup X \mid X \in \mathscr{B}\}$? If not, then under what conditions does equality hold?
