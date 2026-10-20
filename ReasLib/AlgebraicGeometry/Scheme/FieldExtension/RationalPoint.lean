module

public import ReasLib.AlgebraicGeometry.Scheme.FieldExtension.Over
public import ReasLib.AlgebraicGeometry.Scheme.OverField.Point

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.FieldExtension

/-- The `k'`-point `x_{k'}` of the field-extension base change `X_{k'}`, as a morphism
from `Spec k'`. -/
noncomputable def rationalPointBaseChange
    {k k' : Type u} [Field k] [Field k'] [Algebra k k']
    {X : SchemeOverField k} (x : SchemeOverField.point k ⟶ X) :
    Spec (CommRingCat.of k') ⟶ (FieldExtension.Over.baseChange k k' X).left :=
  pullback.lift
    (FieldExtension.specMap k k' ≫ inv (SchemeOverField.point k).hom ≫ x.left)
    (𝟙 (Spec (CommRingCat.of k')))
    (by
      simp only [Category.assoc, Over.w, IsIso.inv_hom_id,
        Category.comp_id, Category.id_comp])

/-- The base-changed point is a section of `X_{k'} ⟶ Spec k'`. -/
theorem rationalPointBaseChange_comp_hom
    {k k' : Type u} [Field k] [Field k'] [Algebra k k']
    {X : SchemeOverField k} (x : SchemeOverField.point k ⟶ X) :
    rationalPointBaseChange x ≫ (FieldExtension.Over.baseChange k k' X).hom =
      𝟙 (Spec (CommRingCat.of k')) :=
  sorry

/-- Projecting `x_{k'}` back to `X` recovers the composite of `x` with `Spec k' ⟶ Spec k`. -/
theorem rationalPointBaseChange_comp_toSource
    {k k' : Type u} [Field k] [Field k'] [Algebra k k']
    {X : SchemeOverField k} (x : SchemeOverField.point k ⟶ X) :
    rationalPointBaseChange x ≫ FieldExtension.toSource k k' X.hom =
      FieldExtension.specMap k k' ≫ inv (SchemeOverField.point k).hom ≫ x.left :=
  sorry

end AlgebraicGeometry.FieldExtension
