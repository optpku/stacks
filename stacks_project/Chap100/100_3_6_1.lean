module

public import ReasLib.CategoryTheory.Bicategory.Limits.Cospan.Hom.Construction
public import ReasLib.CategoryTheory.Fibered.TwoFibreProduct.FullSubbicategory.Functoriality.Coherence.Target
public import stacks_project.Chap94.Definition_94_12_1_Representable

/-!
# Whiskering of self-fibre-product comparison cells along an atlas square

The identity `τ ★ id_pr_R = id_g ★ τ'` for the self 2-fibre products of an atlas
`f : U ⟶ X` and of its base change along `g : X' ⟶ X`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Bicategory
open scoped Bicategory CategoryTheory.TwoFibreProduct

noncomputable section

universe u

namespace AlgebraicGeometry.Groupoids

variable {S : Scheme.{u}} {U X X' : GroupoidsOver S}

/-- The cospan transformation `(snd f g, snd f g) ⟶ (f, f)` induced by the
2-cartesian square of `g : X' ⟶ X` against `f : U ⟶ X`. Its left and right
legs are `fst f g`, its base is `g`, and both comparison cells are
`comparisonIso f g`. -/
def selfFibreCospan (f : U ⟶ X) (g : X' ⟶ X) :
    CospanTransform (TwoFibreProduct.snd.{u + 1, u, u + 1, u} f g)
      (TwoFibreProduct.snd.{u + 1, u, u + 1, u} f g) f f :=
  CospanTransform.mk (TwoFibreProduct.fst.{u + 1, u, u + 1, u} f g)
    (TwoFibreProduct.fst.{u + 1, u, u + 1, u} f g) g
    (TwoFibreProduct.comparisonIso.{u + 1, u, u + 1, u} f g)
    (TwoFibreProduct.comparisonIso.{u + 1, u, u + 1, u} f g)

/-- The left vertex of `selfFibreCospan f g` is the projection `pr_U = fst f g`. -/
theorem selfFibreCospan_left (f : U ⟶ X) (g : X' ⟶ X) :
    (selfFibreCospan f g).left = TwoFibreProduct.fst.{u + 1, u, u + 1, u} f g :=
  sorry

/-- The right vertex of `selfFibreCospan f g` is the projection `pr_U = fst f g`. -/
theorem selfFibreCospan_right (f : U ⟶ X) (g : X' ⟶ X) :
    (selfFibreCospan f g).right = TwoFibreProduct.fst.{u + 1, u, u + 1, u} f g :=
  sorry

/-- The base vertex of `selfFibreCospan f g` is the morphism `g : X' ⟶ X`. -/
theorem selfFibreCospan_base (f : U ⟶ X) (g : X' ⟶ X) :
    (selfFibreCospan f g).base = g :=
  sorry

/-- The left generating comparison of `selfFibreCospan f g` is `comparisonIso f g`. -/
theorem selfFibreCospan_leftIso (f : U ⟶ X) (g : X' ⟶ X) :
    (selfFibreCospan f g).leftIso =
      TwoFibreProduct.comparisonIso.{u + 1, u, u + 1, u} f g :=
  sorry

/-- The right generating comparison of `selfFibreCospan f g` is `comparisonIso f g`. -/
theorem selfFibreCospan_rightIso (f : U ⟶ X) (g : X' ⟶ X) :
    (selfFibreCospan f g).rightIso =
      TwoFibreProduct.comparisonIso.{u + 1, u, u + 1, u} f g :=
  sorry

/-- The arrow projection `pr_R : R' ⟶ R` from `R' = U' ×_{X'} U'` to `R = U ×_X U`,
induced by `selfFibreCospan f g`. -/
def arrowProjection (f : U ⟶ X) (g : X' ⟶ X) :
    TwoFibreProduct.apex.{u + 1, u, u + 1, u}
        (TwoFibreProduct.snd.{u + 1, u, u + 1, u} f g)
        (TwoFibreProduct.snd.{u + 1, u, u + 1, u} f g) ⟶
      TwoFibreProduct.apex.{u + 1, u, u + 1, u} f f :=
  TwoFibreProduct.map (selfFibreCospan f g)

/-- `arrowProjection f g` is the two-fibre-product map of `selfFibreCospan f g`. -/
theorem arrowProjection_eq (f : U ⟶ X) (g : X' ⟶ X) :
    arrowProjection f g = TwoFibreProduct.map (selfFibreCospan f g) :=
  sorry

/-- 100.3.6.1: For morphisms `f : U ⟶ X` and `g : X' ⟶ X` of categories fibred in
groupoids over `S`, write `τ = comparisonIso f f` on `R = apex f f`,
`τ' = comparisonIso (snd f g) (snd f g)` on `R' = apex (snd f g) (snd f g)`,
`pr_R = arrowProjection f g`, `t = fst f f`, `s = snd f f`, `f' = snd f g`, and
`pr_U = fst f g`. Then `τ ★ id_pr_R = id_g ★ τ'` holds after the canonical
associators and the projection comparisons of `pr_R`. In Lean, Stacks
`τ ★ id_pr_R` is `whiskerLeftIso pr_R τ` and Stacks `id_g ★ τ'` is
`whiskerRightIso τ' g`. -/
@[stacks 04Y7]
theorem selfComparison_whisker_eq (f : U ⟶ X) (g : X' ⟶ X) :
    let psi := selfFibreCospan f g
    let f' := TwoFibreProduct.snd.{u + 1, u, u + 1, u} f g
    TwoFibreProduct.map.comparisonIso psi =
      whiskerRightIso (TwoFibreProduct.map.fstIso psi) f ≪≫
        α_ (TwoFibreProduct.fst.{u + 1, u, u + 1, u} f' f') psi.left f ≪≫
        whiskerLeftIso (TwoFibreProduct.fst.{u + 1, u, u + 1, u} f' f') psi.leftIso ≪≫
        (α_ (TwoFibreProduct.fst.{u + 1, u, u + 1, u} f' f') f' psi.base).symm ≪≫
        whiskerRightIso (TwoFibreProduct.comparisonIso.{u + 1, u, u + 1, u} f' f')
          psi.base ≪≫
        α_ (TwoFibreProduct.snd.{u + 1, u, u + 1, u} f' f') f' psi.base ≪≫
        whiskerLeftIso (TwoFibreProduct.snd.{u + 1, u, u + 1, u} f' f')
          psi.rightIso.symm ≪≫
        (α_ (TwoFibreProduct.snd.{u + 1, u, u + 1, u} f' f') psi.right f).symm ≪≫
        whiskerRightIso (TwoFibreProduct.map.sndIso psi).symm f :=
  sorry

end AlgebraicGeometry.Groupoids

