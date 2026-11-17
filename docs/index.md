# Cubical Bicategories

In Cubical Agda, a **path** expresses equality. A category is **univalent** when paths between two objects correspond to isomorphisms between them. We use *precategory* for a category whose object type is arbitrary. Ordinary Rezk completion takes such a category $C$ to a univalent category $\operatorname{RC}_1(C)$.

What happens when we consider all small precategories at once? They form a bicategory, $\mathrm{CAT}$, whose objects are precategories, whose arrows (1-cells) are functors, and whose arrows between functors (2-cells) are natural transformations. To obtain the bicategory $\mathrm{UNIVCAT}$ of univalent categories, we first **localize** $\mathrm{CAT}$ to turn weak equivalences of categories into equivalences in the bicategory. We then take the **bicategorical Rezk completion**, written $\operatorname{RC}_2$. Each step has its own universal property. [Definitions of the bicategories](../src/Bicategories/Instances/Categories.lagda.md)

## Rezk completion of a bicategory

For objects $x$ and $y$ of a bicategory $B$, the hom-category $B(x,y)$ has the arrows from $x$ to $y$ as objects and the 2-cells between them as morphisms. First keep the objects of $B$ and apply ordinary Rezk completion to each hom-category. In the new homs, paths between parallel arrows correspond to invertible 2-cells. Call the resulting bicategory $L$. This correspondence between paths and invertible 2-cells is **local univalence**. The universal property of ordinary completion extends composition to the new arrows, and the triangle and pentagon laws follow by checking them on the original arrows. [Ordinary completion](../src/Bicategories/Categories/RezkCompletion.lagda.md) · [Homwise construction](../src/Bicategories/RezkCompletion/Local.lagda.md)

The next step gives **global univalence**. A path between objects then corresponds to an adjoint equivalence, an arrow with an inverse up to coherent invertible 2-cells. The Yoneda embedding represents an object $x$ of $L$ by the assignment $a \mapsto L(a,x)$. Its full essential image consists of these representations and everything equivalent to one. Although the ambient bicategory of presheaves is large, paths between represented objects can be described by adjoint equivalences in $L$. Cubical’s replacement construction uses these descriptions to give the image a small object type. Evaluation at the identity arrow identifies its hom-categories on representables with the small hom-categories we started with. [Yoneda image](../src/Bicategories/RezkCompletion/Construction/Yoneda.lagda.md) · [Resizing the image](../src/Bicategories/Smallness/Bicategory.lagda.md) · [Cubical replacement](https://github.com/agda/cubical/blob/c37782bb4e382dc41035e0970409a0c17b55e6ce/Cubical/HITs/Replacement/Base.agda)

**Every bicategory $B$ has a univalent completion $\operatorname{RC}_2(B)$ and a canonical map $B \to \operatorname{RC}_2(B)$, called the unit.** The unit is a **weak biequivalence**. On each hom-category it is fully faithful and essentially surjective, and each object of the completion is merely adjoint equivalent to an object in the image. Here *merely* means that the theorem asserts existence while leaving the witness unspecified. In Agda this is called propositional truncation. Univalence and higher inductive types in Cubical Agda suffice for this construction. [Construction and unit](../src/Bicategories/RezkCompletion/Construction/Small.lagda.md)

The construction also controls size. Write $o$, $h$, and $c$ for the universe levels of objects, arrows between fixed objects, and 2-cells between fixed arrows, respectively. The completion has levels $(o \sqcup h \sqcup c, h \sqcup c, c)$, where $\sqcup$ is the maximum. This preserves both a uniform bound and the profile $(\ell+1, \ell, \ell)$ of small categories. For example, take the bicategory with one object, one 1-cell, and the group of order two as its 2-automorphisms. Those two automorphisms have distinct images under the unit. [Universe bounds](../src/Bicategories/RezkCompletion/Construction/Resize.lagda.md?plain=1#L39) · [Double delooping and proof for the unit](../src/Bicategories/Examples/DoubleDelooping.lagda.md?plain=1#L89)

**Universal property.** Given a univalent bicategory $E$, every pseudofunctor $B \to E$ extends along the unit to $\operatorname{RC}_2(B) \to E$. A pseudofunctor preserves composition and identities up to coherent isomorphism. Once the extension is equipped with a pseudonatural equivalence from its restriction to the original pseudofunctor, it is unique up to a unique path. In the formal statement this type of extensions is *contractible*. Restriction also gives equivalences on the categories of pseudonatural transformations and their modifications. Together these statements say that precomposition with the unit gives the following biequivalence of pseudofunctor bicategories, where $\eta_B$ denotes the unit.

$$
\eta_B^* \colon \operatorname{PsFun}(\operatorname{RC}_2(B),E)
    \longrightarrow \operatorname{PsFun}(B,E),
\qquad \widehat F \longmapsto \widehat F \circ \eta_B .
$$

The proof constructs the extension and its comparison with the given pseudofunctor. [Universal property](../src/Bicategories/RezkCompletion/UniversalProperty.lagda.md)

Consequently, a weak biequivalence $B \to C$ gives a biequivalence between their completions compatible with both units. At matching universe levels it gives an equality $\operatorname{RC}_2(B) = \operatorname{RC}_2(C)$ along which the units agree. Completing a univalent bicategory at its own profile gives it back. The construction builds on Kobe Wullaert’s homwise completion and the univalent Yoneda image of Benedikt Ahrens, Dan Frumin, Marco Maggesi, Niccolò Veltri, and Niels van der Weide. [Invariance](../src/Bicategories/RezkCompletion/Construction/Properties.lagda.md) · [Idempotence](../src/Bicategories/RezkCompletion/Comparison.lagda.md?plain=1#L68) · [Wullaert](https://hott-uf.github.io/2023/HoTTUF_2023_paper_5222.pdf) · [Bicategories in Univalent Foundations](https://arxiv.org/abs/1903.01152)

## Localization by fractions

A functor is a **weak equivalence of categories** if it is fully faithful (bijective on each hom-set) and essentially surjective (every target object is merely isomorphic to an image object). To invert these functors, represent an arrow from $G$ to $H$ by a **roof** $G \xleftarrow{w} K \xrightarrow{f} H$. The left leg is a weak equivalence, so the roof acts by following the inverse of the left leg in the localization and then the right leg. An ordinary functor gives a roof with identity left leg. [Roofs and the inclusion of functors](../src/Bicategories/Localization/Fractions/Base.lagda.md)

To compose two roofs, pair objects of their middle categories whose images in the shared category are isomorphic, recording the isomorphism. This gives the *iso-comma category* at the middle of the composite roof. A 2-cell between roofs is a natural transformation after pulling their right legs back to a common refinement. This construction applies to any class of small categories closed under these iso-comma constructions, including all precategories, strict categories, groupoids, and strict groupoids. [Iso-comma construction](../src/Bicategories/Localization/Fractions/IsoComma.lagda.md) · [Roof composition](../src/Bicategories/Localization/Fractions/Composition.lagda.md)

Each roof induces a functor $\operatorname{RC}_1(G) \to \operatorname{RC}_1(H)$, and every such functor has a roof presentation. This gives a second, biequivalent model with the same objects, in which a hom-category is simply the category of functors between two ordinary completions. We write $\operatorname{Frac}$ for this model in the equalities below because it keeps the homs in the required universe. [Small homs](../src/Bicategories/Localization/Fractions/SmallHoms.lagda.md) · [Comparison of the two models](../src/Bicategories/Localization/Fractions/Transfer.lagda.md)

**Universal property.** Let $J$ be the map into the localization and $D$ any bicategory. A pseudofunctor $F$ from the source into $D$ that supplies inverse data for the image of every marked arrow merely admits an extension along $J$, together with a pseudonatural equivalence comparing its restriction to $F$. Between any two pseudofunctors out of the localization, restriction induces an equivalence on the category of transformations and modifications. If $D$ is locally univalent, mere existence of inverse data for each marked arrow suffices. [Localization of a marked bicategory](../src/Bicategories/Localization/Base.lagda.md) · [Proof for both fraction models](../src/Bicategories/Localization/Fractions/UniversalProperty.lagda.md)

## From precategories to univalent categories

Fix a universe level $\ell$ for the small categories. Ordinary completion is left biadjoint to the inclusion $\mathrm{UNIVCAT} \to \mathrm{CAT}$. Concretely, if $U$ is univalent, restricting along $C \to \operatorname{RC}_1(C)$ gives an equivalence of functor categories $\operatorname{Fun}(\operatorname{RC}_1(C),U)\simeq\operatorname{Fun}(C,U)$, natural in both $C$ and $U$. [The biadjunction](../src/Bicategories/Applications/Categories/Reflection.lagda.md)

At the level of bicategories, ordinary completion factors through the following two maps.

$$
\mathrm{CAT} \xrightarrow{J} \operatorname{Frac}(\mathrm{CAT})
   \xrightarrow{\eta} \operatorname{RC}_2(\operatorname{Frac}(\mathrm{CAT}))
   = \mathrm{UNIVCAT}.
$$

The first map inverts weak equivalences of categories. The second is the bicategorical completion unit. Under the displayed equality their composite is ordinary completion, sending each $C$ to $\operatorname{RC}_1(C)$. Consequently, for a univalent bicategory $D$, restriction along $\mathrm{CAT} \to \mathrm{UNIVCAT}$ gives a weak biequivalence onto the full subbicategory of pseudofunctors $\mathrm{CAT} \to D$ that invert weak equivalences. [Completion of fractions](../src/Bicategories/Applications/Categories/Completion.lagda.md?plain=1#L36) · [Identification of the unit](../src/Bicategories/Applications/Categories/Completion.lagda.md?plain=1#L67) · [Composite universal property](../src/Bicategories/Localization/RezkCompletion.lagda.md?plain=1#L93)

Completing $\mathrm{CAT}$ directly gives a different answer. Wullaert observed that $\operatorname{RC}_2(\mathrm{CAT})$ and $\mathrm{UNIVCAT}$ are inequivalent. Our proof uses the one-object groupoid $G$ whose automorphism group has order two. A weak biequivalence $\mathrm{CAT} \to \mathrm{UNIVCAT}$ would supply a functor back from $\operatorname{RC}_1(G)$ to $G$ that splits the completion unit up to natural isomorphism. The nonidentity automorphism rules out such a splitting. It follows that $\mathrm{CAT}$ and $\operatorname{Frac}(\mathrm{CAT})$ are also inequivalent, since a weak biequivalence would identify their completions. [Wullaert’s abstract](https://hott-uf.github.io/2023/HoTTUF_2023_paper_5222.pdf) · [Obstruction theorem](../src/Bicategories/Applications/Categories/Obstruction.lagda.md?plain=1#L173)

The same example distinguishes two functor categories. For any $C,D$, the canonical comparison $\operatorname{RC}_1(\operatorname{Fun}(C,D)) \to \operatorname{Fun}(C, \operatorname{RC}_1(D))$ is fully faithful. It is an equivalence exactly when every functor $C \to \operatorname{RC}_1(D)$ merely lifts to a functor $C \to D$ up to natural isomorphism. For the pair $(G, 1)$, where $1$ is the terminal category, the comparison is an equivalence. For $(\operatorname{RC}_1(G), G)$, the identity functor on $\operatorname{RC}_1(G)$ has no such lift. [Lifting criterion](../src/Bicategories/Applications/Categories/FunctorComparison.lagda.md?plain=1#L76) · [Counterexamples](../src/Bicategories/Examples/TerminalComparison.lagda.md?plain=1#L201)

## Strict categories and groupoids

A category is **strict** here if its objects form a set, so any two proofs of equality between the same objects are equal. Write $\mathrm{STRICTCAT}$ for the full subbicategory of $\mathrm{CAT}$ on these categories. Completing its fractions gives the equality

$$
\operatorname{RC}_2(\operatorname{Frac}(\mathrm{STRICTCAT})) = \mathrm{REPRUNIVCAT}.
$$

The objects of $\mathrm{REPRUNIVCAT}$ are the univalent categories admitting a **strict presentation**, meaning there merely exists a weak equivalence from a strict category. Such a presentation exists exactly when the object type admits a small set cover, a surjection onto it from a small set. [Strict fraction computation](../src/Bicategories/Applications/Categories/Completion.lagda.md?plain=1#L41) · [Characterization of strict presentations](../src/Bicategories/Applications/Presentation.lagda.md?plain=1#L76)

Three canonical maps describe what happens to arrows and objects.

- **From strict categories to their fractions.** The localization unit from $\mathrm{STRICTCAT}$ to $\operatorname{Frac}(\mathrm{STRICTCAT})$ is a weak biequivalence exactly when set-based choice $\mathrm{AC}_0$ holds. This principle says that a family of merely inhabited small sets indexed by a small set merely admits a choice function. It supplies simultaneous representatives for the objects of a functor, so the functor between completions lifts up to natural isomorphism to a functor between strict categories. [Proof of the choice criterion](../src/Bicategories/Applications/Categories/Completion/Maps.lagda.md?plain=1#L113) · [Lifting argument](../src/Bicategories/Applications/Choice.lagda.md?plain=1#L198)
- **From strictly representable to all univalent categories.** The inclusion of $\mathrm{REPRUNIVCAT}$ in $\mathrm{UNIVCAT}$ is biessentially surjective exactly when sets cover small 1-types. Biessential surjectivity here means that every univalent category is merely adjoint equivalent to one with a strict presentation. The cover condition says that each small 1-type (a type whose path types are sets) merely admits a surjection from a small set. Under this cover condition, the completion of $\operatorname{Frac}(\mathrm{STRICTCAT})$ equals $\mathrm{UNIVCAT}$. [Cover criterion for the inclusion](../src/Bicategories/Applications/Categories/Completion/Maps.lagda.md?plain=1#L52) · [Proof of both directions](../src/Bicategories/Applications/Presentation.lagda.md?plain=1#L125) · [Completion under covers](../src/Bicategories/Applications/Categories/Completion.lagda.md?plain=1#L51)
- **From strict categories directly to univalent categories.** The ordinary completion map $\mathrm{STRICTCAT} \to \mathrm{UNIVCAT}$ is a weak biequivalence exactly when both $\mathrm{AC}_0$ and the cover condition hold. Choice accounts for functors between completed categories, and covers account for which categories occur as objects. Together they identify $\operatorname{RC}_2(\mathrm{STRICTCAT})$ with $\mathrm{UNIVCAT}$. [Proof of the combined criterion](../src/Bicategories/Applications/Categories/Completion/Maps.lagda.md?plain=1#L146) · [Completion under both hypotheses](../src/Bicategories/Applications/Categories/Completion.lagda.md?plain=1#L57)

A **groupoid** is a category in which every arrow is invertible. The same comparisons hold for groupoids, with the same criteria on the canonical maps. In particular, $\operatorname{RC}_2(\operatorname{Frac}(\mathrm{GPD})) = \mathrm{UNIVGPD}$, and $\mathrm{AC}_0$ together with set covers of 1-types gives $\operatorname{RC}_2(\mathrm{STRICTGPD}) = \mathrm{UNIVGPD}$. The computed equalities for categories and groupoids identify their completion units with the stated comparison maps. [Groupoid fraction computation](../src/Bicategories/Applications/Groupoids/Completion.lagda.md?plain=1#L39) · [Strict groupoid computation](../src/Bicategories/Applications/Groupoids/Completion.lagda.md?plain=1#L60) · [Concrete instances](../src/Bicategories/Instances/SmallCompletions.lagda.md)

## Typechecking

Use [Agda 2.9.0](https://github.com/agda/agda/releases/tag/v2.9.0) and [Cubical revision `c37782b`](https://github.com/agda/cubical/tree/c37782bb4e382dc41035e0970409a0c17b55e6ce). Register the Cubical checkout’s `cubical.agda-lib` with Agda once. [Library registration](https://agda.readthedocs.io/en/latest/tools/package-system.html#installing-libraries)

Import `Bicategories` to use the public API. To typecheck every module, run this command from the repository root.

```sh
agda -Werror src/Bicategories/Everything.agda
```

## AI disclosure

This project was developed with assistance from an LLM.
