/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.ModuleCat.AB
public import ReasLib.CategoryTheory.Abelian.GrothendieckAxioms.FunctorCategory
public import ReasLib.CategoryTheory.DerivedCategory.Limit.Sequential.Single.Grothendieck
public import ReasLib.CategoryTheory.DerivedCategory.Limit.Tensor.PseudoCoherent
import Mathlib.Tactic.CrossRefAttribute

/-!
# Pseudo-coherent tensoring and the standard module derived limit

This leaf specializes homotopy-limit preservation to the canonical total right derived inverse
limit of a sequential system of modules embedded in degree zero.  It is the notation-independent
owner behind statements written as `K ⊗ᴸ R lim Mₙ`.

@stack 0D2L
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

-- Local instance justification (instance diamond): pin the standard model only in this
-- specialization; the generic limit API keeps its model explicit and exports no competing model.
attribute [local instance] HasDerivedCategory.standard

universe u

namespace CategoryTheory.DerivedLimit

variable {R : Type u} [CommRing R]

/-- Stacks 0D2L: tensoring the standard derived inverse limit of a module tower by a
pseudo-coherent fixed left factor gives a homotopy limit of the stagewise tensor tower. -/
@[stacks 0D2L "pseudo-coherent tensor commutes with the standard module derived limit"]
theorem tensorSingleOfIsPseudoCoherent
    {K : DerivedCategory (ModuleCat.{u} R)} (hK : K.IsPseudoCoherent)
    (M : SequentialInverseSystem (ModuleCat.{u} R)) :
    HomotopyLimit.IsOf
      ((M ⋙ ModuleCat.single0Functor) ⋙
        DerivedCategory.DerivedTensor.Bifunctor.leftFunctor K)
      ((DerivedCategory.DerivedTensor.Bifunctor.leftFunctor K).obj
        ((functor (ModuleCat.{u} R)).obj
          ((DerivedCategory.singleFunctor
            (SequentialInverseSystem (ModuleCat.{u} R)) (0 : ℤ)).obj M))) := sorry

end CategoryTheory.DerivedLimit
