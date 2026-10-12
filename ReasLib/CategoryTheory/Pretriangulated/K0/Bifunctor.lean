/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Pretriangulated.K0.GrothendieckGroup
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Bifunctorial Maps on Triangulated Grothendieck Groups

A bifunctor that is triangulated in each variable induces a biadditive map on
zeroth Grothendieck groups.  This construction is independent of any monoidal
interpretation of the bifunctor.
-/

open CategoryTheory.Limits

universe v₁ u₁ v₂ u₂ v₃ u₃

namespace CategoryTheory.TriangulatedK0.Bifunctor

variable {D₁ : Type u₁} [Category.{v₁} D₁] [Preadditive D₁]
  [HasZeroObject D₁] [HasShift D₁ ℤ]
  [∀ n : ℤ, Functor.Additive (shiftFunctor D₁ n)] [Pretriangulated D₁]
variable {D₂ : Type u₂} [Category.{v₂} D₂] [Preadditive D₂]
  [HasZeroObject D₂] [HasShift D₂ ℤ]
  [∀ n : ℤ, Functor.Additive (shiftFunctor D₂ n)] [Pretriangulated D₂]
variable {D₃ : Type u₃} [Category.{v₃} D₃] [Preadditive D₃]
  [HasZeroObject D₃] [HasShift D₃ ℤ]
  [∀ n : ℤ, Functor.Additive (shiftFunctor D₃ n)] [Pretriangulated D₃]

variable (F : D₁ ⥤ D₂ ⥤ D₃)
variable [∀ X : D₁, (F.obj X).CommShift ℤ]
variable [∀ X : D₁, (F.obj X).IsTriangulated]
variable [∀ Y : D₂, (F.flip.obj Y).CommShift ℤ]
variable [∀ Y : D₂, (F.flip.obj Y).IsTriangulated]

/-- Relations in the first variable vanish under the raw family of K₀ maps
induced by a bifunctor that is triangulated in both variables. -/
theorem relations_le_ker :
    relations D₁ ≤
      (FreeAbelianGroup.lift fun X ↦ TriangulatedK0.map (F.obj X)).ker := sorry

/-- Stacks 0FCT: a bifunctor triangulated in each variable induces a
biadditive map on triangulated zeroth Grothendieck groups. -/
@[stacks 0FCT]
def map : TriangulatedK0 D₁ →+ TriangulatedK0 D₂ →+ TriangulatedK0 D₃ :=
  TriangulatedK0.lift
    (fun X ↦ TriangulatedK0.map (F.obj X)) (relations_le_ker F)

/-- Fixing an object class in the first variable recovers the K₀ map induced
by the corresponding one-variable functor. -/
@[simp]
theorem map_of_left (X : D₁) :
    map F (TriangulatedK0.of X) = TriangulatedK0.map (F.obj X) := sorry

/-- The bifunctorial map sends a pair of object classes to the class of the
bifunctor value. -/
@[stacks 0FCT, simp]
theorem map_of (X : D₁) (Y : D₂) :
    map F (TriangulatedK0.of X) (TriangulatedK0.of Y) =
      TriangulatedK0.of ((F.obj X).obj Y) := sorry

/-- Fixing an object class in the second variable recovers the K₀ map induced
by the flipped one-variable functor. -/
@[simp]
theorem flip_map_of (Y : D₂) :
    AddMonoidHom.flip (map F) (TriangulatedK0.of Y) =
      TriangulatedK0.map (F.flip.obj Y) := sorry

end CategoryTheory.TriangulatedK0.Bifunctor
