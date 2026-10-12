/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Adjunction.FullyFaithful
public import Mathlib.CategoryTheory.ObjectProperty.ContainsZero
public import Mathlib.CategoryTheory.Triangulated.Adjunction
import Mathlib.Tactic.CrossRefAttribute

/-!
# Fully faithful triangulated adjunctions with zero right-adjoint kernel

For a fully faithful triangulated left adjoint, a zero-kernel condition on the right adjoint first
forces the counit components to be invertible, then essential surjectivity, and finally an
equivalence.  The three conclusions are exposed separately for downstream use.
-/

@[expose] public section

open CategoryTheory.Limits
open CategoryTheory.Pretriangulated

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.Adjunction.ZeroKernel

variable {D : Type u₁} [Category.{v₁} D] [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
variable {D' : Type u₂} [Category.{v₂} D'] [HasZeroObject D'] [HasShift D' ℤ] [Preadditive D']
  [∀ n : ℤ, (shiftFunctor D' n).Additive] [Pretriangulated D']
variable {F : D ⥤ D'} {G : D' ⥤ D}
  [F.CommShift ℤ] [F.IsTriangulated]

section FullyFaithful

variable [F.Full] [F.Faithful]

/-- Stacks 09J1: if the right adjoint has zero kernel, every counit component of a fully faithful
triangulated left adjoint is an isomorphism. -/
@[stacks 09J1 "zero-kernel counit criterion"]
theorem counit_isIso (adj : F ⊣ G) (hker : G.kernel ≤ IsZero) (X : D') :
    IsIso (adj.counit.app X) := sorry

/-- Stacks 09J1: a fully faithful triangulated left adjoint is essentially surjective when its
right adjoint has zero kernel. -/
@[stacks 09J1 "zero-kernel essential surjectivity"]
theorem essSurj (adj : F ⊣ G) (hker : G.kernel ≤ IsZero) :
    F.EssSurj := sorry

/-- Stacks 09J1, Lemma 13.7.2: a fully faithful triangulated left adjoint whose right adjoint has
zero kernel is an equivalence. -/
@[stacks 09J1]
theorem isEquivalence (adj : F ⊣ G) (hker : G.kernel ≤ IsZero) :
    F.IsEquivalence := sorry

end FullyFaithful

/-- A triangulated left adjoint is essentially surjective when its unit is pointwise invertible
and its right adjoint has zero kernel. -/
theorem essSurj_of_isIso_unit
    (adj : F ⊣ G) (hunit : ∀ X : D, IsIso (adj.unit.app X))
    (hker : G.kernel ≤ IsZero) : F.EssSurj := sorry

/-- A triangulated left adjoint is an equivalence when its unit is pointwise invertible and its
right adjoint has zero kernel. -/
theorem isEquivalence_of_isIso_unit
    (adj : F ⊣ G) (hunit : ∀ X : D, IsIso (adj.unit.app X))
    (hker : G.kernel ≤ IsZero) : F.IsEquivalence := sorry

end CategoryTheory.Adjunction.ZeroKernel
