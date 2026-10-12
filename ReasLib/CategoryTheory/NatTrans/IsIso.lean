/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.MorphismProperty.Basic
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Isomorphism Loci of Natural Transformations

The isomorphism locus of a natural transformation is invariant along a source morphism whenever
both functors send that morphism to an isomorphism. This form is useful for localization arguments:
the source morphism itself need not be an isomorphism.
-/

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.NatTrans

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
variable {F G : C ⥤ D} (α : F ⟶ G)

/-- The objects at which a natural transformation is an isomorphism. -/
@[stacks 0BZ3 "isomorphism locus of a natural transformation"]
abbrev isomorphismLocus : ObjectProperty C :=
  fun X ↦ IsIso (α.app X)

/-- A natural transformation is an isomorphism exactly when its isomorphism locus is the whole
source category. -/
theorem isIso_iff_isomorphismLocus_eq_top :
    IsIso α ↔ isomorphismLocus α = ⊤ := sorry

/-- If both functors invert `f`, then the component of `α` at the source of `f` is an
isomorphism exactly when its component at the target is. -/
@[stacks 015M "transport of a natural-transformation isomorphism locus"]
theorem isIso_app_iff_of_map_isIso {X Y : C} (f : X ⟶ Y)
    [IsIso (F.map f)] [IsIso (G.map f)] :
    IsIso (α.app X) ↔ IsIso (α.app Y) := sorry

end CategoryTheory.NatTrans
