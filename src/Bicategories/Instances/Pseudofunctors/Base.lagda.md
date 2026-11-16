# The pseudofunctor bicategory

For bicategories $B$ and $D$, the diagrams $B\to D$ themselves form a bicategory. Its arrows are pseudonatural transformations between diagrams and its 2-cells are modifications between transformations.

```agda
{-# OPTIONS --lossy-unification #-}
module Bicategories.Instances.Pseudofunctors.Base where

open import Cubical.Foundations.Prelude hiding (comp)
open import Bicategories.Base
open import Bicategories.Pseudofunctor.Base
open import Bicategories.PseudonaturalTransformation.Base
open import Bicategories.PseudonaturalTransformation.Identity
open import Bicategories.Modification.Base
open import Bicategories.Modification.Horizontal
open import Bicategories.Instances.Pseudofunctors.Coherence

module _ {o h c r s t} (B : Bicategory o h c) (D : Bicategory r s t) where
  private module D = Bicategory D
  open Bicategory
  open BicategoryStructure
  open Pseudofunctor
  open PseudonaturalTransformation
  open Modification

```

For fixed $F,G:B\to D$, the hom-category consists of pseudonatural transformations $F\Rightarrow G$ and their modifications. Its objects compose by pasting their naturality squares. The resulting identity, composition, unitors and associator supply the first fields of `PSFUN`.

```agda
  PSFUN : Bicategory (ℓ-max (ℓ-max o (ℓ-max h c)) (ℓ-max r (ℓ-max s t)))
                     (ℓ-max (ℓ-max o (ℓ-max h c)) (ℓ-max s t))
                     (ℓ-max (ℓ-max o h) t)
  PSFUN .Ob = Pseudofunctor B D
  PSFUN .hom = transformationCategory
  PSFUN .structure .id₁ = identityTransformation
  PSFUN .structure .comp {F} {G} {H} = composeFunctor F G H
  PSFUN .structure .leftUnitor = transformationLeftUnitor
  PSFUN .structure .rightUnitor = transformationRightUnitor
  PSFUN .structure .associator = transformationAssociator
```

To compare two modifications, it suffices to compare their components at each $x$ in $B$. For example, the pentagon on four transformations reduces to the pentagon in $D$ on $\alpha_x,\beta_x,\gamma_x,\delta_x$. Each use of `modificationPath` makes this pointwise argument.

```agda
  PSFUN .structure .leftUnitor-natural {F} {G} m =
    modificationPath {F = F} {G = G} (funExt λ x →
      D.leftUnitor-natural (m .at x))
  PSFUN .structure .rightUnitor-natural {F} {G} m =
    modificationPath {F = F} {G = G} (funExt λ x →
      D.rightUnitor-natural (m .at x))
  PSFUN .structure .associator-natural {F} {G} {H} {K} m n l =
    modificationPath {F = F} {G = K} (funExt λ x →
      D.associator-natural (m .at x) (n .at x) (l .at x))
  PSFUN .structure .triangle {F} {G} {H} α β =
    modificationPath {F = F} {G = H} (funExt λ x →
      D.triangle (α .component x) (β .component x))
  PSFUN .structure .pentagon {F} {G} {H} {K} {L} α β γ δ =
    modificationPath {F = F} {G = L} (funExt λ x →
      D.pentagon (α .component x) (β .component x) (γ .component x) (δ .component x))
  PSFUN .structure .unitors-id F =
    modificationPath {F = F} {G = F} (funExt λ x → D.unitors-id (F .F₀ x))
```
