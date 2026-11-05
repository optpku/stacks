/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.FieldExtension.Over
public import ReasLib.AlgebraicGeometry.Scheme.OverField.Point

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

namespace AlgebraicGeometry.FieldExtension

/-- The `k'`-point `x_{k'}` of the field-extension base change `X_{k'}`, as a morphism
from `Spec k'`. The map to the chosen field point is supplied by its terminal
universal property. -/
noncomputable def rationalPointBaseChange
    {k k' : Type u} [Field k] [Field k'] [Algebra k k']
    {X : SchemeOverField k} (x : SchemeOverField.point k ⟶ X) :
    Spec (CommRingCat.of k') ⟶ (FieldExtension.Over.baseChange k k' X).left := by
  let p : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ SchemeOverField.point k :=
    terminal.from _
  exact pullback.lift
    (FieldExtension.specMap k k' ≫ p.left ≫ x.left)
    (𝟙 (Spec (CommRingCat.of k')))
    (by
      simp only [Category.assoc, Over.w x, Category.id_comp]
      rw [Over.w p]
      exact Category.comp_id _)

/-- The base-changed point is a section of `X_{k'} ⟶ Spec k'`. -/
theorem rationalPointBaseChange_comp_hom
    {k k' : Type u} [Field k] [Field k'] [Algebra k k']
    {X : SchemeOverField k} (x : SchemeOverField.point k ⟶ X) :
    rationalPointBaseChange x ≫ (FieldExtension.Over.baseChange k k' X).hom =
      𝟙 (Spec (CommRingCat.of k')) := by
  change rationalPointBaseChange x ≫ pullback.snd X.hom (FieldExtension.specMap k k') = _
  unfold rationalPointBaseChange
  exact pullback.lift_snd _ _ _

/-- Projecting `x_{k'}` back to `X` recovers the composite of `x` with `Spec k' ⟶ Spec k`. -/
theorem rationalPointBaseChange_comp_toSource
    {k k' : Type u} [Field k] [Field k'] [Algebra k k']
    {X : SchemeOverField k} (x : SchemeOverField.point k ⟶ X) :
    rationalPointBaseChange x ≫ FieldExtension.toSource k k' X.hom =
      FieldExtension.specMap k k' ≫ inv (SchemeOverField.point k).hom ≫ x.left := by
  let p : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ SchemeOverField.point k :=
    terminal.from _
  letI := SchemeOverField.pointHomIsIso k
  have hp : p.left = inv (SchemeOverField.point k).hom :=
    IsIso.eq_inv_of_inv_hom_id (f := (SchemeOverField.point k).hom) (Over.w p)
  change rationalPointBaseChange x ≫ pullback.fst _ _ = _
  simp only [rationalPointBaseChange, pullback.lift_fst]
  change FieldExtension.specMap k k' ≫ p.left ≫ x.left = _
  rw [hp]

end AlgebraicGeometry.FieldExtension
