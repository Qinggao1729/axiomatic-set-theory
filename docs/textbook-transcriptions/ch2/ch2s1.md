# Chapter 2 Section 1 (Axioms)

Source: Enderton, *Elements of Set Theory*, pp. 17-23.

**page 17**

In this chapter we begin by introducing the first six of our ten axioms. Initially the axiomatization might appear to be like cumbersome machinery to accomplish simple tasks. But we trust that it will eventually prove itself to be powerful machinery for difficult tasks. Of course the axioms are not chosen at random, but must ultimately reflect our informal ideas about what sets are.

In addition to the introduction of basic concepts, this chapter provides practice in using the symbolic notation introduced in Chapter 1. Finally the chapter turns to the standard results on the algebra of sets.

## AXIOMS

The first of our axioms is the principle of extensionality.

**Extensionality Axiom** If two sets have exactly the same members, then they are equal:

$$\forall A\ \forall B[\forall x(x \in A \iff x \in B) \implies A = B].$$

**page 18**

The above symbolic rendering of extensionality is the one we developed previously. We will supply similar symbolizations for the other axioms. The more practice the better!

Next we need some axioms assuring the existence of some basic sets that were encountered informally in the preceding chapter.

**Empty Set Axiom** There is a set having no members:

$$\exists B\ \forall x\ x \notin B.$$

**Pairing Axiom** For any sets $u$ and $v$, there is a set having as members just $u$ and $v$:

$$\forall u\ \forall v\ \exists B\ \forall x(x \in B \iff x = u \text{ or } x = v).$$

**Union Axiom, Preliminary Form** For any sets $a$ and $b$, there is a set whose members are those sets belonging either to $a$ or to $b$ (or both):

$$\forall a\ \forall b\ \exists B\ \forall x(x \in B \iff x \in a \text{ or } x \in b).$$

**Power Set Axiom** For any set $a$, there is a set whose members are exactly the subsets of $a$:

$$\forall a\ \exists B\ \forall x(x \in B \iff x \subseteq a).$$

Here we can, if we wish, rewrite "$x \subseteq a$" in terms of the definition of $\subseteq$:

$$\forall t(t \in x \implies t \in a).$$

Later we will expand this list to include

| | |
| --- | --- |
| subset axioms, | replacement axioms, |
| infinity axiom, | regularity axiom, |
| choice axiom. | |

Also the union axiom will be restated in a stronger form. (Not all of these axioms are really necessary; some will be found to be redundant.)

The set existence axioms can now be used to justify the definition of symbols used informally in Chapter 1. First of all, we want to define the symbol "$\varnothing$."

**Definition** $\varnothing$ is the set having no members.

This definition bestows the name "$\varnothing$" on a certain set. But when we write down such a definition there are two things of which we must be sure: We must know that there exists a set having no members, and we must know that there cannot be more than one set having no members. The empty set axiom provides the first fact, and extensionality provides the second. Without both facts the symbol "$\varnothing$" would not be well defined. Severe logical difficulties arise from introducing symbols when either there is no object for the symbol to name, or (even worse) the symbol names ambiguously more than one object.

**page 19**

The other set existence axioms justify the definition of the following symbols.

**Definition** (i) For any sets $u$ and $v$, the *pair set* $\{u, v\}$ is the set whose only members are $u$ and $v$.

(ii) For any sets $a$ and $b$, the *union* $a \cup b$ is the set whose members are those sets belonging either to $a$ or to $b$ (or both).

(iii) For any set $a$, the *power set* $\mathscr{P}a$ is the set whose members are exactly the subsets of $a$.

As with the empty set, our set existence axioms assure us that the sets being named exist, and extensionality assures us that the sets being named are unique.

We can use pairing and union together to form other finite sets. First of all, given any $x$ we have the *singleton* $\{x\}$, which is defined to be $\{x, x\}$. And given any $x_1$, $x_2$, and $x_3$ we can define

$$\{x_1, x_2, x_3\} = \{x_1, x_2\} \cup \{x_3\}.$$

Similarly we can define $\{x_1, x_2, x_3, x_4\}$, and so forth.

Having defined the union operation, we should accompany it by the intersection operation. But to justify the definition of intersection we need new axioms, to which we now turn. In the next few paragraphs we shall use our informal view of sets to motivate the formulation of these axioms.

Observe that our set existence axioms contain expressions like "there is a set $B$ whose members are those sets $x$ satisfying the condition $\_\_$," where the blank is filled by some condition specifying which sets we want. In symbols this becomes

$$\exists B\ \forall x(x \in B \iff \_\_).$$

If the axiom mentions some other sets $t_1, \ldots, t_k$, then the full version becomes

$$\forall t_1 \cdots \forall t_k\ \exists B\ \forall x(x \in B \iff \_\_)$$

with the blank filled by some expression involving $t_1, \ldots, t_k$, and $x$. The empty set axiom is not quite in this form, but it can be rewritten as

$$\exists B\ \forall x(x \in B \iff x \neq x),$$

which is in the above form (with $k = 0$). The set $B$ whose existence is asserted by such an axiom is (by extensionality) uniquely determined by $t_1, \ldots, t_k$, so we can give it a name (in which the symbols $t_1, \ldots, t_k$ appear). This is just what we have done.

**page 20**

Now let us try to be more general and consider any sentence $\sigma$ of the form

$$\forall t_1 \cdots \forall t_k\ \exists B\ \forall x(x \in B \iff \_\_),$$

where the blank is filled by some expression involving at most $t_1, \ldots, t_k$, and $x$. If this sentence is true, then the set $B$ could be named by use of the abstraction notation of Chapter 1:

$$B = \{x \mid \_\_\}.$$

The sets recently defined can be named by use of the abstraction notation:

$$\varnothing = \{x \mid x \neq x\},$$
$$\{u, v\} = \{x \mid x = u \text{ or } x = v\},$$
$$a \cup b = \{x \mid x \in a \text{ or } x \in b\},$$
$$\mathscr{P}a = \{x \mid x \subseteq a\}.$$

One might be tempted to think that *any* sentence $\sigma$ of the form

$$\forall t_1 \cdots \forall t_k\ \exists B\ \forall x(x \in B \iff \_\_)$$

should be adopted as true. But this is wrong; some sentences of this form are false in our informal view of sets (Chapter 1). For example,

$$\exists B\ \forall x(x \in B \iff x = x)$$

is false, since it asserts the existence of a set $B$ to which every set belongs. The most that can be said is that there is a *class* $\mathbf{A}$ (but not necessarily a set) whose members are those *sets* $x$ such that $\_\_$:

$$\mathbf{A} = \{x \mid \_\_\}.$$

In order for the class $\mathbf{A}$ to be a set it must be included in some level $V_\alpha$ of the hierarchy. In fact it is enough for $\mathbf{A}$ to be included in any set $c$, for then

$$\mathbf{A} \subseteq c \subseteq V_\alpha$$

for some $\alpha$, and from this it follows that $\mathbf{A} \in V_{\alpha+1}$.

All this is to motivate the adoption of the subset axioms. These axioms say, very roughly, that any class $\mathbf{A}$ included in some *set* $c$ must in fact be a set. But the axioms can refer (in the Zermelo–Fraenkel alternative) only to sets. So instead of direct reference to the class $\mathbf{A}$, we refer instead to the expression $\_\_$ that defined $\mathbf{A}$.

**page 21**

**Subset Axioms** For each formula $\_\_$ not containing $B$, the following is an axiom:

$$\forall t_1 \cdots \forall t_k\ \forall c\ \exists B\ \forall x(x \in B \iff x \in c\ \&\ \_\_).$$

In English, the axiom asserts (for any $t_1, \ldots, t_k$ and $c$) the existence of a set $B$ whose members are exactly those sets $x$ in $c$ such that $\_\_$. It then follows automatically that $B$ is a subset of $c$ (whence the name "subset axiom"). The set $B$ is uniquely determined (by $t_1, \ldots, t_k$ and $c$), and can be named by use of a variation on the abstraction notation:

$$B = \{x \in c \mid \_\_\}.$$

*Example* One of the subset axioms is:

$$\forall a\ \forall c\ \exists B\ \forall x(x \in B \iff x \in c\ \&\ x \in a).$$

This axiom asserts the existence of the set we define to be the *intersection* $c \cap a$ of $c$ and $a$.

We are not tied to one particular choice of letters. For example, we will also allow as a subset axiom:

$$\forall A\ \forall B\ \exists S\ \forall t[t \in S \iff t \in A\ \&\ t \notin B].$$

This set $S$ is the *relative complement* of $B$ in $A$, denoted $A - B$.

*Note on Terminology* The subset axioms are often known by the name Zermelo gave them, *Aussonderung axioms*. The word *Aussonderung* is German, and is formed from *sonderen* (to separate) and *aus* (out).

*Example* In Chapter 4 we shall construct the set $\omega$ of natural numbers:

$$\omega = \{0, 1, 2, \ldots\}.$$

We will then be able to use the subset axioms to form the set of even numbers and the set of primes:

$$\{x \in \omega \mid x \text{ is even}\} \quad \text{and} \quad \{y \in \omega \mid y \text{ is prime}\}.$$

(But to do this we must be able to express "$x$ is even" by means of a legal formula; we will return to this point shortly.)

*Example* Let $s$ be some set. Then there is a set $Q$ whose members are the one-element subsets of $s$:

$$Q = \{a \in \mathscr{P}s \mid a \text{ is a one-element subset of } s\}.$$

We can now use the argument of Russell's paradox to show that the *class* $\mathbf{V}$ of all sets is not itself a set.

**page 22**

**Theorem 2A** There is no set to which every set belongs.

*Proof* Let $A$ be a set; we will construct a set not belonging to $A$. Let

$$B = \{x \in A \mid x \notin x\}.$$

We claim that $B \notin A$. We have, by the construction of $B$,

$$B \in B \iff B \in A\ \&\ B \notin B.$$

If $B \in A$, then this reduces to

$$B \in B \iff B \notin B,$$

which is impossible, since one side must be true and the other false. Hence $B \notin A$. $\dashv$

One might ask whether a set can ever be a member of itself. We will argue much later (in Chapter 7) that it cannot. And consequently in the preceding proof, the set $B$ is actually the same as the set $A$.

At this point we need to say just what a formula is. After all, it would be most unfortunate to have as one of the subset axioms

$$\exists B\ \forall x(x \in B \iff x \in \omega\ \&\ x \text{ is an integer definable in one line of type}).$$

We are saved from this disaster by our logical symbols. By insisting that the formula be expressible in the formal language these symbols give us, we can eliminate "$x$ is an integer definable in one line of type" from the list of possible formulas. (Moral: Those symbols are your friends!)

The simplest formulas are expressions such as

$$a \in B \quad \text{and} \quad a = b$$

(and similarly with other letters). More complicated formulas can then be built up from these by use of the expressions

$$\forall x, \quad \exists x, \quad \neg, \quad \&, \quad \text{or}, \quad \Rightarrow, \quad \Leftrightarrow,$$

together with enough parentheses to avoid ambiguity. That is, from formulas $\varphi$ and $\psi$ we can construct longer formulas $\forall x\ \varphi$, $\exists x\ \varphi$ (and similarly $\forall y\ \varphi$, etc.), $(\neg\varphi)$, $(\varphi\ \&\ \psi)$, $(\varphi \text{ or } \psi)$, $(\varphi \Rightarrow \psi)$, and $(\varphi \Leftrightarrow \psi)$. We define a *formula* to be a string of symbols constructed from the simplest formulas by use of the above-listed methods. For example,

$$\exists x(x \in A\ \&\ \forall t(t \in x \implies (\neg t \in A)))$$

is a formula. In practice, however, we are likely to abbreviate it by something a little more readable, such as

$$(\exists x \in A)(\forall t \in x)\ t \notin A.$$

**page 23**

An ungrammatical string of symbols such as $)) \Rightarrow A$ is not a formula, nor is

$$x \text{ is an integer definable in one line of type}.$$

*Example* Let $s$ be some set. In a previous example we formed the set of one-element subsets of $s$:

$$\{a \in \mathscr{P}s \mid a \text{ is a one-element subset of } s\}.$$

Now "$a$ is a one-element subset of $s$" is not itself a formula, but it can be rewritten as a formula. As a first step, it can be expressed as

$$a \subseteq s\ \&\ a \neq \varnothing\ \&\ \text{any two members of } a \text{ coincide}.$$

This in turn becomes the formula

$$((\forall x(x \in a \implies x \in s)\ \&\ \exists y\ y \in a)\ \&\ \forall u\ \forall v((u \in a\ \&\ v \in a) \implies u = v)).$$

In applications of subset axioms we generally will not write out the formula itself. And this example shows why; "$a$ is a one-element subset of $s$" is much easier to read than the legal formula. But in every case it will be possible (for a person with unbounded patience) to eliminate the English words and the defined symbols (such as $\varnothing$, $\cup$, and so forth) in order to arrive at a legal formula. The procedure for eliminating defined symbols is discussed further in the Appendix.
