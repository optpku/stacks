/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Pretriangulated.K0.Universal
public import Mathlib.CategoryTheory.Triangulated.Adjunction

@[expose] public section

/-!
# Triangulated Grothendieck Groups and Equivalences

An exact equivalence of pretriangulated categories induces a bijection on
their zeroth triangulated Grothendieck groups.
-/

open CategoryTheory.Limits
open CategoryTheory.Pretriangulated

universe v₁ u₁ v₂ u₂

namespace CategoryTheory.TriangulatedK0

variable {C₁ : Type u₁} [Category.{v₁} C₁] [Preadditive C₁] [HasZeroObject C₁]
  [HasShift C₁ ℤ] [∀ n : ℤ, Functor.Additive (shiftFunctor C₁ n)] [Pretriangulated C₁]
variable {C₂ : Type u₂} [Category.{v₂} C₂] [Preadditive C₂] [HasZeroObject C₂]
  [HasShift C₂ ℤ] [∀ n : ℤ, Functor.Additive (shiftFunctor C₂ n)] [Pretriangulated C₂]

/-- The homomorphism on triangulated zeroth Grothendieck groups induced by an
exact equivalence is bijective. -/
theorem map_bijective (F : C₁ ⥤ C₂) [F.CommShift ℤ] [F.IsTriangulated]
    [F.IsEquivalence] : Function.Bijective (map F) := sorry

end CategoryTheory.TriangulatedK0
