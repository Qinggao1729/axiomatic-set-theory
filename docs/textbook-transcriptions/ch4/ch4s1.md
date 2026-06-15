# Chapter 4 Section 1 (Inductive Sets)

Source: Enderton, *Elements of Set Theory*, pp. 67-70.

**page 67**

## INDUCTIVE SETS

First we need to define natural numbers as suitable sets. Now numbers do not at first glance appear to be sets. Not that it is an easy matter to say what numbers *do* appear to be. They are abstract concepts, which are slippery things to handle. (See, for example, the section on "Two" in Chapter 5.) Nevertheless, we can construct specific sets that will serve perfectly well as numbers. In fact this can be done in a variety of ways. In 1908, Zermelo proposed to use

$$\varnothing, \quad \{\varnothing\}, \quad \{\{\varnothing\}\}, \ldots$$

as the natural numbers. Later von Neumann proposed an alternative, which has several advantages and has become standard. The guiding principle behind von Neumann's construction is to make each natural number be the set of all smaller natural numbers. Thus we define the first four natural numbers as follows:

$$0 = \varnothing,$$
$$1 = \{\varnothing\} = \{0\},$$
$$2 = \{0, 1\} = \{\varnothing, \{\varnothing\}\},$$
$$3 = \{0, 1, 2\} = \{\varnothing, \{\varnothing\}, \{\varnothing, \{\varnothing\}\}\}.$$

We could continue in this way to define 17 or any chosen natural number. Notice, for example, that the set 3 has three members. It has been selected from the class of all three-member sets to represent the size of the sets in that class.

This construction of the numbers as sets involves some extraneous properties that we did not originally expect. For example,

$$0 \in 1 \in 2 \in 3 \in \cdots$$

and

$$0 \subseteq 1 \subseteq 2 \subseteq 3 \subseteq \cdots.$$

But these properties can be regarded as accidental side effects of the definition. They do no harm, and actually will be convenient at times.

Although we have defined the first four natural numbers, we do not yet have a definition of what it means in general for something to be a natural number. That is, we have not defined the set of all natural numbers. Such a definition cannot rely on linguistic devices such as three dots or phrases like "and so forth." First we define some preliminary concepts.

**page 68**

**Definition** For any set $a$, its *successor* $a^+$ is defined by

$$a^+ = a \cup \{a\}.$$

A set $A$ is said to be *inductive* iff $\varnothing \in A$ and it is "closed under successor," i.e.,

$$(\forall a \in A)\ a^+ \in A.$$

In terms of the successor operation, the first few natural numbers can be characterized as

$$0 = \varnothing, \quad 1 = \varnothing^+, \quad 2 = \varnothing^{++}, \quad 3 = \varnothing^{+++}, \ldots.$$

These are all distinct, e.g., $\varnothing^+ \neq \varnothing^{+++}$ (Exercise 1). And although we have not yet given a formal definition of "infinite," we can see informally that any inductive set will be infinite.

We have as yet no axioms that provide for the existence of infinite sets. There are indeed infinitely many distinct sets whose existence we could establish. But there is no one set having infinitely many members that we can prove to exist. Consequently we cannot yet prove that any inductive set exists. We now correct that fault.

**Infinity Axiom** There exists an inductive set:

$$(\exists A)[\varnothing \in A\ \&\ (\forall a \in A)\ a^+ \in A].$$

Armed with this axiom, we can now define the concept of natural number.

**Definition** A *natural number* is a set that belongs to every inductive set.

We next prove that the collection of all natural numbers constitutes a set.

**Theorem 4A** There is a set whose members are exactly the natural numbers.

*Proof* Let $A$ be an inductive set; by the infinity axiom it is possible to find such a set. By a subset axiom there is a set $w$ such that for any $x$,

$$x \in w \iff x \in A\ \&\ x \text{ belongs to every other inductive set}$$
$$\iff x \text{ belongs to every inductive set}.$$

(This proof is essentially the same as the proof of Theorem 2B.) $\dashv$

**page 69**

The set of all natural numbers is denoted by a lowercase Greek omega:

$$x \in \omega \iff x \text{ is a natural number}$$
$$\iff x \text{ belongs to every inductive set}.$$

In terms of classes, we have

$$\omega = \bigcap\{A \mid A \text{ is inductive}\},$$

but the class of all inductive sets is not a set.

**Theorem 4B** $\omega$ is inductive, and is a subset of every other inductive set.

*Proof* First of all, $\varnothing \in \omega$ because $\varnothing$ belongs to every inductive set. And second,

$$a \in \omega \implies a \text{ belongs to every inductive set}$$
$$\implies a^+ \text{ belongs to every inductive set}$$
$$\implies a^+ \in \omega.$$

Hence $\omega$ is inductive. And clearly $\omega$ is included in every other inductive set. $\dashv$

Since $\omega$ is inductive, we know that $0\ (=\varnothing)$ is in $\omega$. It then follows that $1\ (=0^+)$ is in $\omega$, as are $2\ (=1^+)$ and $3\ (=2^+)$. Thus 0, 1, 2, and 3 are natural numbers. Unnecessary extraneous objects have been excluded from $\omega$, since $\omega$ is the *smallest* inductive set. This fact can also be restated as follows.

**Induction Principle for $\omega$** Any inductive subset of $\omega$ coincides with $\omega$.

Suppose, for example, that we want to prove that for every natural number $n$, the statement $\_\_ n \_\_$ holds. We form the set

$$T = \{n \in \omega \mid \_\_ n \_\_\}$$

of natural numbers for which the desired conclusion is true. If we can show that $T$ is inductive, then the proof is complete. Such a proof is said to be a *proof by induction*. The next theorem gives a very simple example of this method.

**Theorem 4C** Every natural number except 0 is the successor of some natural number.

*Proof* Let $T = \{n \in \omega \mid \text{either } n = 0 \text{ or } (\exists p \in \omega)\ n = p^+\}$. Then $0 \in T$. And if $k \in T$, then $k^+ \in T$. Hence by induction, $T = \omega$. $\dashv$

**page 70**

## Exercise

See also the Review Exercises at the end of this chapter.

**1.** Show that $1 \neq 3$, i.e., that $\varnothing^+ \neq \varnothing^{+++}$.
