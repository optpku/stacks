/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Functor.HomologicalKernel.Localization
public import ReasLib.CategoryTheory.MorphismProperty.Triangulated.Calculus
public import ReasLib.CategoryTheory.MorphismProperty.SaturatedMultiplicativeSystem
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# The Triangulated Morphism Property of a Homological Kernel

The morphisms detected as isomorphisms by every shift of a homological functor
form the canonical saturated denominator system associated to its kernel.
-/

open CategoryTheory Limits

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.Functor.HomologicalKernel

variable {D : Type u₁} {A : Type u₂}
  [Category.{v₁} D] [Category.{v₂} A]
  [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
  [Abelian A]

/-- The cone-defined morphism property of a homological kernel is compatible with the
pretriangulated structure. -/
noncomputable instance compatible
    (H : D ⥤ A) [H.IsHomological] [H.ShiftSequence ℤ] :
    H.homologicalKernel.trW.IsCompatibleWithTriangulation := sorry

/-- Stacks 05R5: the morphisms inducing isomorphisms under every shifted value of a homological
functor form a saturated multiplicative system. -/
@[stacks 05R5]
noncomputable instance saturated
    (H : D ⥤ A) [H.IsHomological] [H.ShiftSequence ℤ] :
    MorphismProperty.IsSaturatedMultiplicativeSystem H.homologicalKernel.trW := sorry

end CategoryTheory.Functor.HomologicalKernel
