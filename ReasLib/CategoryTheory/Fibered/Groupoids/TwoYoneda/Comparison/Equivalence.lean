module

import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.Fibered.BasedCategory.Equivalence.Bicategorical
public import ReasLib.CategoryTheory.Fibered.Groupoids.TwoYoneda.Comparison.Construction

/-!
# Equivalence induced by two-Yoneda evaluation

This file proves that evaluation at the identity is an equivalence on every fiber and hence on
the total categories. It separately packages the result as a bicategorical equivalence when the
source and target lie in one saturated `BasedCategory C` owner.
-/

@[expose] public section

universe v u vS uS vAux uAux

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]
variable {S : Type uS} [Category.{vS} S]

namespace TwoYoneda.splitToOriginal

/- Axiom audit: `#print axioms` leaves `BasedCategory.overMap` free of `sorryAx`.
`BasedCategory.precomposition` and the later functorial data report `sorryAx` only through the
named identity, composition, projection, and slice-triangle proofs stored in law/coherence
fields. Their object functions, morphism functions, co-Grothendieck pairs, and evaluation maps
are all explicit; no carrier, map, inverse, or witness is supplied by `sorry`. -/

/-- On every fiber, the comparison is the evaluation equivalence of Lemma 4.41.2. -/
instance fiberFunctor_isEquivalence
    (p : S ⥤ C) [Functor.IsFibered.InGroupoids p] (U : C) :
    (BasedFunctor.fiberFunctor (splitToOriginal p) U).IsEquivalence := sorry
/- Proof strategy: identify the canonical `HasFibers.inducedFunctor` for the
co-Grothendieck projection with `TwoYoneda.presheaf p` at `U`; under this equivalence the fiber
map is evaluation at `𝟙 U`. Use the universe-polymorphic evaluation argument of Lemma 4.41.2
(or transport that theorem through category lifts until its universes are generalized), then
cancel the induced equivalence. -/

/-- Remark 4.41.3 (Stacks 076J): evaluation at the identity from the `2`-Yoneda
co-Grothendieck model is an equivalence over the base. The instance is universe-polymorphic; in a
saturated fixed owner, `splitToOriginal.equivalence` selects the corresponding bicategorical
equivalence. -/
@[stacks 076J]
instance isEquivalence
    (p : S ⥤ C) [Functor.IsFibered.InGroupoids p] :
    (splitToOriginal p).IsEquivalence := sorry
/- Proof strategy: use the preceding fiberwise evaluation equivalences and the criterion of
Lemma 4.35.9, then package the heterogeneous total equivalence with
`BasedFunctor.IsEquivalence.mk'`. -/

section SaturatedOwner

open scoped Bicategory

variable {Sₛ : Type (max uAux (max vAux (max u v)))}
  [Category.{max vAux (max u v)} Sₛ]

/-- The bicategorical equivalence selected from evaluation at the identity when source and target
lie in the same saturated `BasedCategory C` owner. -/
@[stacks 076J "2-Yoneda equivalence with the original fibred category"]
noncomputable def equivalence
    (p : Sₛ ⥤ C) [Functor.IsFibered.InGroupoids p] :
    splitModel p ≌ BasedCategory.ofFunctor p :=
  (splitToOriginal p).asEquivalence

namespace equivalence

/-- The forward morphism of `splitToOriginal.equivalence p` is evaluation at the identity. -/
@[simp]
theorem hom
    (p : Sₛ ⥤ C) [Functor.IsFibered.InGroupoids p] :
    (equivalence.{v, u, vAux, uAux} p).hom =
      splitToOriginal p := sorry
/- Proof strategy: apply `BasedFunctor.asEquivalence.hom`. -/

/-- The inverse morphism of the saturated `2`-Yoneda equivalence is the named inverse selected
by the based equivalence-over-base API. -/
@[simp]
theorem inv
    (p : Sₛ ⥤ C) [Functor.IsFibered.InGroupoids p] :
    (equivalence.{v, u, vAux, uAux} p).inv =
      (splitToOriginal p).inv := sorry
/- Proof strategy: apply `BasedFunctor.asEquivalence.inv`. -/

/-- The unit of the saturated `2`-Yoneda equivalence is the canonical adjustment of the selected
based unit against the selected based counit. -/
theorem unit
    (p : Sₛ ⥤ C) [Functor.IsFibered.InGroupoids p] :
    (equivalence.{v, u, vAux, uAux} p).unit =
      Bicategory.Equivalence.adjointifyUnit
        (splitToOriginal p).unitIso (splitToOriginal p).counitIso := sorry
/- Proof strategy: apply `BasedFunctor.asEquivalence.unit`. -/

/-- The counit of the saturated `2`-Yoneda equivalence is the selected based counit of evaluation
at the identity. -/
@[simp]
theorem counit
    (p : Sₛ ⥤ C) [Functor.IsFibered.InGroupoids p] :
    (equivalence.{v, u, vAux, uAux} p).counit =
      (splitToOriginal p).counitIso := sorry
/- Proof strategy: apply `BasedFunctor.asEquivalence.counit`. -/

end equivalence

end SaturatedOwner

end TwoYoneda.splitToOriginal

end CategoryTheory
