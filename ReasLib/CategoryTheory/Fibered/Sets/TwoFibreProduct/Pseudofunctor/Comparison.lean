module

public import ReasLib.CategoryTheory.Fibered.Sets.TwoFibreProduct.Pseudofunctor.Action
public import ReasLib.CategoryTheory.Bicategory.Limits.Cospan.Bundled.Map

/-!
# Comparison readouts for set-fibred two-fibre products

This leaf exposes both directions of the identity and composition comparisons after forgetting
to based categories, together with the factorization of the complete pseudofunctor.
-/

@[expose] public section

noncomputable section

universe u v w vB

namespace CategoryTheory

open Bicategory
open scoped Bicategory

variable {C : Type u} [Category.{v} C]

namespace FiberedCategoryOver.Sets.TwoFibreProduct

/-- The forward identity comparison is the neutral selected two-fibre-product comparison after
forgetting to based categories. -/
@[simp]
theorem pseudofunctor.mapId.hom.toBased
    (S : Bicategory.Cospan
      (FiberedCategoryOver.Sets.{u, v, max w (max u (max v vB)), max v vB} C)) :
    ((pseudofunctor C).mapId S).hom.hom =
      (_root_.CategoryTheory.TwoFibreProduct.map.idIso S.fst S.snd).hom.hom := sorry

/-- The inverse identity comparison is the neutral selected two-fibre-product comparison after
forgetting to based categories. -/
theorem pseudofunctor.mapId.inv.toBased
    (S : Bicategory.Cospan
      (FiberedCategoryOver.Sets.{u, v, max w (max u (max v vB)), max v vB} C)) :
    ((pseudofunctor C).mapId S).inv.hom ≍
      (_root_.CategoryTheory.TwoFibreProduct.map.idIso S.fst S.snd).inv.hom := sorry

/-- The forward composition comparison is the neutral selected two-fibre-product comparison
after forgetting to based categories. -/
theorem pseudofunctor.mapComp.hom.toBased
    {R S T : Bicategory.Cospan
      (FiberedCategoryOver.Sets.{u, v, max w (max u (max v vB)), max v vB} C)}
    (psi : R ⟶ S) (phi : S ⟶ T) :
    ((pseudofunctor C).mapComp psi phi).hom.hom ≍
      (_root_.CategoryTheory.TwoFibreProduct.map.compIso
        (Bicategory.Cospan.Hom.toCospanTransform psi)
        (Bicategory.Cospan.Hom.toCospanTransform phi)).hom.hom := sorry

/-- The inverse composition comparison is the neutral selected two-fibre-product comparison
after forgetting to based categories. -/
theorem pseudofunctor.mapComp.inv.toBased
    {R S T : Bicategory.Cospan
      (FiberedCategoryOver.Sets.{u, v, max w (max u (max v vB)), max v vB} C)}
    (psi : R ⟶ S) (phi : S ⟶ T) :
    ((pseudofunctor C).mapComp psi phi).inv.hom ≍
      (_root_.CategoryTheory.TwoFibreProduct.map.compIso
        (Bicategory.Cospan.Hom.toCospanTransform psi)
        (Bicategory.Cospan.Hom.toCospanTransform phi)).inv.hom := sorry

/-- Forgetting the discrete-fibration witnesses after set-fibred two-fibre products gives the
componentwise based-cospan map followed by the explicit based pseudo-pullback pseudofunctor. -/
theorem pseudofunctor.comp_toBased :
    (pseudofunctor C).comp
        (FiberedCategoryOver.Sets.toBased C).toPseudofunctor =
      (Bicategory.Cospan.map
          (FiberedCategoryOver.Sets.toBased C).toPseudofunctor).comp
        (BasedCategory.PseudoPullback.pseudofunctor C) := sorry

end FiberedCategoryOver.Sets.TwoFibreProduct

end CategoryTheory
