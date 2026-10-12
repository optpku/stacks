/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Adjunction
public import Mathlib.CategoryTheory.Monoidal.NaturalTransformation
public import ReasLib.Algebra.Category.ModuleCat.ChangeOfRings.Exact

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace ModuleCat

/-- A right-exact, direct-sum-preserving monoidal functor between commutative-ring module
categories is monoidally naturally isomorphic to extension of scalars along a unique ring
homomorphism. -/
theorem monoidalFunctor_isomorphic_extendScalars {A B : Type u} [CommRing A] [CommRing B]
    (F : ModuleCat Aᵐᵒᵖ ⥤ ModuleCat Bᵐᵒᵖ) [F.Monoidal]
    (h_rightExact : rightExactFunctor (ModuleCat Aᵐᵒᵖ) (ModuleCat Bᵐᵒᵖ) F)
    (h_directSums : ∀ J : Type u, PreservesColimitsOfShape (Discrete J) F) :
    ∃! φ : A →+* B, ∃ e : F ≅ ModuleCat.extendScalars φ.op,
      CategoryTheory.NatTrans.IsMonoidal e.hom := sorry

end ModuleCat
