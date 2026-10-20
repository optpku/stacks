module

public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.CategoryTheory.Abelian.Projective.Basic
public import ReasLib.CategoryTheory.Abelian.Projective.Characterizations
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Projective modules and exact represented Hom

The categorical projectivity criterion is owned by
`CategoryTheory.projective_iff_exact_preadditiveCoyonedaObj`.  This leaf adds
only the ModuleCat bridge, so module users do not need to reconstruct
category-theoretic instances in each proof.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits ModuleCat

universe v u

namespace Module.Projective

variable {R : Type u} [Ring R] [Small.{v} R]

/-- An `R`-module is projective exactly when its represented Hom functor on
`ModuleCat R` is exact. -/
@[stacks 05CE "projective module and exact Hom functor"]
theorem iff_exact_hom (P : Type v) [AddCommGroup P] [Module R P] :
    Module.Projective R P ↔
      exactFunctor (ModuleCat R) _ (preadditiveCoyonedaObj (of R P)) := sorry
/- Proof strategy: compose
`CategoryTheory.projective_iff_exact_preadditiveCoyonedaObj (of R P)` with
`IsProjective.iff_projective P`; this keeps all instance construction in the
canonical categorical bridge. -/

end Module.Projective
