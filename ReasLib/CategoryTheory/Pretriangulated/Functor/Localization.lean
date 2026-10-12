/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Triangulated.Functor
public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.MorphismProperty.SaturatedMultiplicativeSystem
public import ReasLib.CategoryTheory.Pretriangulated.Functor.Localization.Lift

@[expose] public section

/-!
# Localization Systems of Triangulated Functors

For a triangulated functor, this leaf identifies the cone-defined system attached to its kernel
with the arrows sent to isomorphisms. It then exposes the resulting saturated multiplicative
systems as canonical instances, so derived and Verdier-localization arguments do not rebuild
fraction calculi locally.
-/

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.Functor

open Limits MorphismProperty ObjectProperty Pretriangulated

variable {D : Type u₁} {D' : Type u₂} [Category.{v₁} D] [Category.{v₂} D']
  [HasZeroObject D] [HasZeroObject D'] [HasShift D ℤ] [HasShift D' ℤ]
  [Preadditive D] [Preadditive D']
  [∀ n : ℤ, (shiftFunctor D n).Additive]
  [∀ n : ℤ, (shiftFunctor D' n).Additive]
  [Pretriangulated D] [Pretriangulated D']

/-- the cone-defined system of an exact functor's kernel consists exactly of the
morphisms the functor sends to isomorphisms. -/
@[stacks 05R4]
theorem kernel_trW_eq_inverseImage_isomorphisms
    (F : D ⥤ D') [F.CommShift ℤ] [F.IsTriangulated] :
    F.kernel.trW = (isomorphisms D').inverseImage F := sorry

/-- the cone-defined system associated to the kernel of an exact functor is a
saturated multiplicative system. -/
@[stacks 05R4]
instance kernel_trW_isSaturatedMultiplicativeSystem
    (F : D ⥤ D') [F.CommShift ℤ] [F.IsTriangulated] :
    F.kernel.trW.IsSaturatedMultiplicativeSystem := sorry

/-- morphisms sent to isomorphisms by an exact functor form a saturated
multiplicative system. -/
@[stacks 05R4]
instance inverseImage_isomorphisms_isSaturatedMultiplicativeSystem
    (F : D ⥤ D') [F.CommShift ℤ] [F.IsTriangulated] :
    ((isomorphisms D').inverseImage F).IsSaturatedMultiplicativeSystem := sorry


end CategoryTheory.Functor
