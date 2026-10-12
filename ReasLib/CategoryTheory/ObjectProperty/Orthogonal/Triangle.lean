/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Localization.Bousfield
public import Mathlib.CategoryTheory.ObjectProperty.Orthogonal
public import Mathlib.CategoryTheory.ObjectProperty.Shift
public import Mathlib.CategoryTheory.Triangulated.Pretriangulated
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Orthogonals and Morphisms in Distinguished Triangles

For a shift-stable object property, orthogonality of an outer object in a distinguished triangle
is equivalent to the corresponding Bousfield local or colocal condition on the adjacent map.
The two directions are exposed symmetrically under the right- and left-orthogonal owners.
-/

@[expose] public section

open CategoryTheory Limits Pretriangulated

universe v u

namespace CategoryTheory.ObjectProperty

variable {D : Type u} [Category.{v} D] [Limits.HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]

namespace RightOrthogonal

/-- Right orthogonality of the third object makes the first triangle map injective on morphisms
from every object satisfying `P`. -/
theorem mor₁_injective (P : ObjectProperty D) [P.IsStableUnderShift ℤ]
    (T : Triangle D) (hT : T ∈ distTriang D) {X : D} (hX : P X)
    (h₃ : P.rightOrthogonal T.obj₃) :
    Function.Injective (fun f : X ⟶ T.obj₁ ↦ f ≫ T.mor₁) := sorry

/-- Right orthogonality of the third object makes the first triangle map surjective on morphisms
from every object satisfying `P`. -/
theorem mor₁_surjective (P : ObjectProperty D) [P.IsStableUnderShift ℤ]
    (T : Triangle D) (hT : T ∈ distTriang D) {X : D} (hX : P X)
    (h₃ : P.rightOrthogonal T.obj₃) :
    Function.Surjective (fun f : X ⟶ T.obj₁ ↦ f ≫ T.mor₁) := sorry

/-- Colocality of the first triangle map forces every morphism from an object satisfying `P` to
the third triangle object to vanish. -/
theorem hom_obj₃_eq_zero_of_colocal (P : ObjectProperty D) [P.IsStableUnderShift ℤ]
    (T : Triangle D) (hT : T ∈ distTriang D) {X : D} (hX : P X)
    (hcol : P.isColocal T.mor₁) (f : X ⟶ T.obj₃) :
    f = 0 := sorry

/-- Stacks 0CQQ: the third object of a distinguished triangle is right-orthogonal to `P`
exactly when its first map is `P`-colocal. -/
@[stacks 0CQQ]
theorem obj₃_iff_colocal (P : ObjectProperty D) [P.IsStableUnderShift ℤ]
    (T : Triangle D) (hT : T ∈ distTriang D) :
    P.rightOrthogonal T.obj₃ ↔ P.isColocal T.mor₁ := sorry

end RightOrthogonal

namespace LeftOrthogonal

/-- Left orthogonality of the first object makes the second triangle map injective on morphisms
to every object satisfying `P`. -/
theorem mor₂_injective (P : ObjectProperty D) [P.IsStableUnderShift ℤ]
    (T : Triangle D) (hT : T ∈ distTriang D) {X : D} (hX : P X)
    (h₁ : P.leftOrthogonal T.obj₁) :
    Function.Injective (fun f : T.obj₃ ⟶ X ↦ T.mor₂ ≫ f) := sorry

/-- Left orthogonality of the first object makes the second triangle map surjective on morphisms
to every object satisfying `P`. -/
theorem mor₂_surjective (P : ObjectProperty D) [P.IsStableUnderShift ℤ]
    (T : Triangle D) (hT : T ∈ distTriang D) {X : D} (hX : P X)
    (h₁ : P.leftOrthogonal T.obj₁) :
    Function.Surjective (fun f : T.obj₃ ⟶ X ↦ T.mor₂ ≫ f) := sorry

/-- Locality of the second triangle map forces every morphism from the first triangle object to
an object satisfying `P` to vanish. -/
theorem hom_obj₁_eq_zero_of_local (P : ObjectProperty D) [P.IsStableUnderShift ℤ]
    (T : Triangle D) (hT : T ∈ distTriang D) {X : D} (hX : P X)
    (hloc : P.isLocal T.mor₂) (f : T.obj₁ ⟶ X) :
    f = 0 := sorry

/-- Stacks 0H0M: the first object of a distinguished triangle is left-orthogonal to `P`
exactly when its second map is `P`-local. -/
@[stacks 0H0M]
theorem obj₁_iff_local (P : ObjectProperty D) [P.IsStableUnderShift ℤ]
    (T : Triangle D) (hT : T ∈ distTriang D) :
    P.leftOrthogonal T.obj₁ ↔ P.isLocal T.mor₂ := sorry

end LeftOrthogonal

end CategoryTheory.ObjectProperty
