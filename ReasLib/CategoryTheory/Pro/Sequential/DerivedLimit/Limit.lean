/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.InverseSystem.Sequential
public import ReasLib.CategoryTheory.Pro.Sequential.CommonRefinement

/-!
# Inverse-limit maps from sequential pro-morphism representatives

A monotone level representative of a sequential pro-morphism induces a map on inverse limits.
The construction depends only on the represented pro-morphism and respects identities and
composition.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

universe u v

namespace CategoryTheory.Pro.SequentialHom

variable {C : Type u} [Category.{v} C]
variable {X Y : SequentialInverseSystem C}
variable [HasLimitsOfShape ℕᵒᵖ C]

/-- The inverse-limit map represented by a monotone sequential pro-morphism representative. -/
noncomputable def limitMap (r : Pro.SequentialHom X Y) :
    limit X ⟶ limit Y :=
  limit.pre X r.reindex.toFunctor.op ≫ lim.map r.hom

/-- The stage-projection formula for `limitMap`. -/
theorem limitMap_π (r : Pro.SequentialHom X Y) (n : ℕ) :
    r.limitMap ≫ limit.π Y (op n) =
      limit.π X (op (r.reindex n)) ≫ r.hom.app (op n) := sorry

/-- Identity representatives induce identity maps on inverse limits. -/
@[simp]
theorem limitMap_id (X : SequentialInverseSystem C) :
    (Pro.SequentialHom.id X).limitMap = 𝟙 (limit X) := sorry

/-- Composition of representatives composes their inverse-limit maps. -/
@[simp]
theorem limitMap_comp {Z : SequentialInverseSystem C}
    (r : Pro.SequentialHom X Y) (s : Pro.SequentialHom Y Z) :
    (Pro.SequentialHom.comp r s).limitMap = r.limitMap ≫ s.limitMap := sorry

/-- Equivalent sequential representatives induce the same inverse-limit map. -/
theorem limitMap_eq_of_toHom_eq
    {r s : Pro.SequentialHom X Y} (h : r.toHom = s.toHom) :
    r.limitMap = s.limitMap := sorry

/-- Common-refinement equivalent representatives induce the same inverse-limit map. -/
theorem limitMap_eq_of_equivalent
    {r s : Pro.SequentialHom X Y} (h : Equivalent r s) :
    r.limitMap = s.limitMap := sorry

end CategoryTheory.Pro.SequentialHom
