module

public import ReasLib.CategoryTheory.Fibered.YonedaEvaluation.TwoFibreProduct.Isomorphism.Collapse.Counit

/-!
# The collapse equivalence

This leaf packages the deterministic inverse, unit, and counit as a bicategorical equivalence.
-/

@[expose] public section

universe u v

namespace CategoryTheory

open Opposite CategoryOfElements
open scoped Bicategory BasedFunctor

variable {C : Type u} [Category.{v} C]

namespace FiberedCategoryOver.TwoFibreProduct.Isomorphism

variable (X : FiberedCategoryOver C) {U : C} (x y : X.p.Fiber U)

namespace collapse

/-- Explicit quasi-inverse data for the collapse. The inverse functor and both comparison
isomorphisms have concrete constructors; only their proof-valued laws are deferred. -/
@[stacks 04SI "collapse quasi-inverse owner"]
noncomputable def quasiInverse :
    BasedFunctor.QuasiInverse (collapse X x y) where
  inverse := inverse X x y
  unitIso := unitIso X x y
  counitIso := counitIso X x y

namespace quasiInverse

/-- The inverse functor retained by the named collapse quasi-inverse is the deterministic
construction. -/
@[simp, stacks 04SI "collapse quasi-inverse inverse readout"]
theorem inverse :
    (quasiInverse X x y).inverse = collapse.inverse X x y := sorry

/-- The named collapse quasi-inverse retains the explicit unit. -/
@[simp, stacks 04SI "collapse quasi-inverse unit readout"]
theorem unitIso :
    (quasiInverse X x y).unitIso = collapse.unitIso X x y := sorry

/-- The named collapse quasi-inverse retains the explicit counit. -/
@[simp, stacks 04SI "collapse quasi-inverse counit readout"]
theorem counitIso :
    (quasiInverse X x y).counitIso = collapse.counitIso X x y := sorry

end quasiInverse

/-- The literal collapse is an equivalence over the slice category, witnessed by its explicit
deterministic quasi-inverse. -/
@[stacks 04SI "literal collapse equivalence instance"]
noncomputable instance isEquivalence :
    (collapse X x y).IsEquivalence := sorry

/-- The explicit bicategorical equivalence between the literal and canonical owners. -/
@[stacks 04SI "literal collapse equivalence"]
noncomputable def equivalence :
    (sourceSetoids X x y).toBasedCategory ≌
      (fibration X x y).toBasedCategory :=
  (quasiInverse X x y).toEquivalence

namespace equivalence

/-- The forward morphism of the collapse equivalence is the canonical collapse. -/
@[simp, stacks 04SI "collapse equivalence forward readout"]
theorem hom :
    (equivalence X x y).hom = collapse X x y := sorry

/-- The inverse morphism of the collapse equivalence is the deterministic reconstruction. -/
@[simp, stacks 04SI "collapse equivalence inverse readout"]
theorem inv :
    (equivalence X x y).inv = inverse X x y := sorry

/-- The unit of the collapse equivalence is the adjointified explicit unit. -/
@[stacks 04SI "collapse equivalence unit readout"]
theorem unit :
    (equivalence X x y).unit =
      Bicategory.Equivalence.adjointifyUnit (unitIso X x y) (counitIso X x y) := sorry

/-- The counit of the collapse equivalence is the explicit collapse counit. -/
@[simp, stacks 04SI "collapse equivalence counit readout"]
theorem counit :
    (equivalence X x y).counit = counitIso X x y := sorry

end equivalence
end collapse
end FiberedCategoryOver.TwoFibreProduct.Isomorphism
end CategoryTheory
