# Dependent pairs of record fields

Some fields of a bicategory are themselves functions with implicit arguments. When passing to a dependent pair of fields, their full function types can be read from the record constructor. This supplies the types of the two projections before Agda elaborates the fieldwise isomorphism.

```agda
{-# OPTIONS --no-exact-split #-}
module Bicategories.StructureIdentity.RecordFields where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism using (Iso)
open import Cubical.Data.List.Base as List
open import Cubical.Data.Unit.Base using (Unit)
open import Cubical.Reflection.Base
open import Cubical.Reflection.RecordEquiv as Fields using (List→ΣFormat; recordName→isoTy; recordIsoΣClauses)
import Agda.Builtin.Reflection as R

private
  telescope : R.Type → R.Type
  telescope (R.pi (R.arg i a) (R.abs _ (R.def _ _))) = a
  telescope (R.pi (R.arg i a) (R.abs x b)) = R.def (quote Σ) (a v∷ vlam x (telescope b) v∷ [])
  telescope _ = R.def (quote Unit) []

```

For fields $a:A$ and $b:B(a)$ the constructor has two successive arguments, and `telescope` represents them by $\sum_{a:A}B(a)$. The parameters of the record, such as its universe levels, remain parameters of the isomorphism. `fieldsType` copies these initial binders and fills in the isomorphism type at the end.

```agda
  fieldsType : R.Type → R.Type → R.TC R.Type
  fieldsType (R.pi a (R.abs x b)) (R.pi _ (R.abs _ t)) =
    liftTC (λ u → R.pi a (R.abs x u)) (fieldsType b t)
  fieldsType (R.def _ (varg a ∷ _ ∷ [])) t =
    R.returnTC (R.def (quote Iso) (a v∷ telescope t v∷ []))
  fieldsType _ _ = R.typeError (R.strErr "Expected a record constructor telescope" ∷ [])

```

Given a record name, read its constructor and its fields in declaration order. The Cubical library supplies the fieldwise isomorphism clauses. We give those clauses the type computed from the constructor, so implicit arguments on individual fields retain their types.

```agda
declareFields : R.Name → R.Name → R.TC Unit
declareFields name recordName = R.getDefinition recordName >>= λ where
  (R.record-type con fields) →
    let format = List→ΣFormat (List.map (λ { (R.arg _ f) → f }) fields)
    in recordName→isoTy recordName format >>= λ withMetas →
       R.getType con >>= fieldsType withMetas >>= λ ty →
       R.declareDef (varg name) ty >> R.defineFun name (recordIsoΣClauses format)
  _ → R.typeError (R.strErr "Expected a record" ∷ [])
```
