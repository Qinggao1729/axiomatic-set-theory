# Ch6 Section 5 (Axiom of Choice) - Literal Transcription

Source: Enderton, *Elements of Set Theory*, Chapter 6, Section 5, pp. 151-158 (PDF pages 161-168).

## Literal transcription

### p.151

At several points in this book we have already encountered the need for a principle asserting the possibility of selecting members from nonempty sets. We can no longer postpone a systematic discussion of such a principle. There are numerous equivalent formulations of the axiom of choice. The following theorem lists six of them.

Theorem 6M. The following statements are equivalent.

(1) Axiom of choice, I. For any relation $R$, there is a function $F \subseteq R$ with $\operatorname{dom} F = \operatorname{dom} R$.

(2) Axiom of choice, II; multiplicative axiom. The Cartesian product of nonempty sets is always nonempty. That is, if $H$ is a function with domain $I$ and if $(\forall i \in I)\, H(i) \neq \varnothing$, then there is a function $f$ with domain $I$ such that $(\forall i \in I)\, f(i) \in H(i)$.

(3) Axiom of choice, III. For any set $A$ there is a function $F$ (a "choice function" for $A$) such that the domain of $F$ is the set of nonempty subsets of $A$, and such that $F(B) \in B$ for every nonempty $B \subseteq A$.

(4) Axiom of choice, IV. Let $\mathcal{A}$ be a set such that (a) each member of $\mathcal{A}$ is a nonempty set, and (b) any two distinct members of $\mathcal{A}$ are disjoint. Then there exists a set $C$ containing exactly one element from each member of $\mathcal{A}$ (i.e., for each $B \in \mathcal{A}$ the set $C \cap B$ is a singleton $\{x\}$ for some $x$).

(5) Cardinal comparability. For any sets $C$ and $D$, either $C \preceq D$ or $D \preceq C$. For any two cardinal numbers $\kappa$ and $\lambda$, either $\kappa \le \lambda$ or $\lambda \le \kappa$.

(6) Zorn's lemma. Let $\mathcal{A}$ be a set such that for every chain $\mathcal{B} \subseteq \mathcal{A}$, we have $\bigcup\mathcal{B} \in \mathcal{A}$. ($\mathcal{B}$ is called a chain iff for any $C$ and $D$ in $\mathcal{B}$, either $C \subseteq D$ or $D \subseteq C$.) Then $\mathcal{A}$ contains an element $M$ (a "maximal" element) such that $M$ is not a subset of any other set in $\mathcal{A}$.

Statements (1)-(4) are synoptic ways of saying that there exist uniform methods for selecting elements from sets. On the other hand, statements (5) and (6) appear to be rather different.

Proof in part. First we will prove that (1)-(4) are equivalent.

### p.152-153

(1) $\Rightarrow$ (2) To prove (2), we assume that $H$ is a function with domain $I$ and that $H(i) \ne \varnothing$ for each $i \in I$. In order to utilize (1), define the relation

$$
R = \{\langle i, x\rangle \mid i \in I \;\&\; x \in H(i)\}.
$$

Then (1) provides us with a function $F \subseteq R$ such that $\operatorname{dom}F = \operatorname{dom}R = I$. Then since $\langle i, F(i)\rangle \in F \subseteq R$, we must have $F(i) \in H(i)$. Thus the conclusion of (2) holds.

(2) $\Rightarrow$ (4) Let $\mathcal{A}$ be a set meeting conditions (a) and (b) of (4). Let $H$ be the identity function on $\mathcal{A}$; then $(\forall B \in \mathcal{A})\, H(B) \ne \varnothing$. Hence by (2) there is a function $f$ with domain $\mathcal{A}$ such that $(\forall B \in \mathcal{A})\, f(B) \in H(B)=B$. Let $C=\operatorname{ran}f$. Then for $B \in \mathcal{A}$ we have $B\cap C=\{f(B)\}$.

(4) $\Rightarrow$ (3) Given a set $A$, define

$$
\mathcal{A} = \{\{B\}\times B \mid B \text{ is a nonempty subset of } A\}.
$$

Then each member of $\mathcal{A}$ is nonempty, and any two distinct members are disjoint. Let $C$ be a set (provided by (4)) whose intersection with each member of $\mathcal{A}$ is a singleton:

$$
C \cap (\{B\}\times B)=\{\langle B,x\rangle\},
$$

where $x\in B$. It is a priori possible that $C$ contains extraneous elements not belonging to any member of $\mathcal{A}$. So discard them by letting $F = C \cap (\bigcup \mathcal{A})$. We claim that $F$ is a choice function for $A$. Any member of $F$ belongs to some $\{B\}\times B$, and hence is of the form $\langle B,x\rangle$ for $x\in B$. For anyone nonempty set $B\subseteq A$, there is a unique $x$ such that $\langle B,x\rangle\in F$, because $F\cap(\{B\}\times B)$ is a singleton. This $x$ is of course $F(B)$ and it is a member of $B$.

(3) $\Rightarrow$ (1) Consider any relation $R$. Then (3) provides us with a choice function $G$ for $\operatorname{ran}R$; thus $G(B)\in B$ for any nonempty subset $B$ of $\operatorname{ran}R$. Then define a function $F$ with $\operatorname{dom}F=\operatorname{dom}R$ by

$$
F(x)=G(\{y\mid xRy\}).
$$

Then $F(x)\in\{y\mid xRy\}$, i.e., $\langle x,F(x)\rangle\in R$. Hence $F\subseteq R$.

It remains to include parts (5) and (6) of the theorem.

(6) $\Rightarrow$ (1) The strategy behind this application (and others) of Zorn's lemma is to form a collection $\mathcal{A}$ of pieces of the desired object, and then to show that a maximal piece serves the intended purpose. In the present case, we are given a relation $R$ and we choose to define

$$
\mathcal{A}=\{f\subseteq R \mid f \text{ is a function}\}.
$$

Before we can appeal to Zorn's lemma, we must check that $\mathcal{A}$ is closed under unions of chains. ... Now we can appeal to (6), which provides us with a maximal function $F$ in $\mathcal{A}$. We claim that $\operatorname{dom}F=\operatorname{dom}R$.

(6) $\Rightarrow$ (5) Let $C$ and $D$ be any sets; we will show that either $C\preceq D$ or $D\preceq C$. In order to utilize (6), define

$$
\mathcal{A}=\{f \mid f \text{ is one-to-one } \&\; \operatorname{dom}f\subseteq C \;\&\; \operatorname{ran}f\subseteq D\}.
$$

Applying (6), obtain maximal $J\in\mathcal{A}$ and conclude either $\operatorname{dom}J=C$ or $\operatorname{ran}J=D$.

At this point we have proved that part of Theorem 6M shown in Fig. 40. The proof will be completed in Chapter 7.

### p.154-155

We now formally add the axiom of choice to our list of axioms.

This is because historically the axiom of choice has had a unique status. Initially some mathematicians objected to the axiom, because it asserts the existence of a set without specifying exactly what is in it. To this extent it is less "constructive" than the other axioms. Gradually the axiom has won acceptance (at least acceptance by most mathematicians willing to accept classical logic). But it retains a slightly tarnished image, from the days when it was not quite respectable. Consequently it has become widespread practice, each time the axiom of choice is used, to make explicit mention of the fact.

In Chapter 7 we will complete our axiomatization by adding the replacement axioms and the regularity axiom.

Without the axiom of choice, we can still prove that for a finite set $I$, if $H(i)\ne\varnothing$ for all $i\in I$, then there is a function $f$ with domain $I$ such that $f(i)\in H(i)$ for all $i\in I$. But for an infinite set $I$, the axiom of choice is indispensable.

## Design plan (repo)

1. Keep primitive axioms with straightforward primitive formulations in `Set/Axioms.lean` (Infinity already there; add Replacement and Regularity there as planned in Ch.7).
2. For AC, follow textbook staging in chapter files: define/use AC forms in-place where they are introduced and used.
3. Because AC is non-constructive and its many equivalent forms depend on prior development (relations/functions/cardinals/Zorn framework), keep each form local to the chapter context where its statement is mathematically motivated.
4. Preserve explicit assumption boundaries by namespacing chapter-local AC forms (e.g. `Set.AppStyle.Choice`) so consumers can see which form is being assumed.
