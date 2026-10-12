/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.Cone
public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.PseudoCone.Bilimit
public import ReasLib.CategoryTheory.Fibered.TwoFibreProduct.FullSubbicategory.Bilimit
public import stacks_project.Chap94.Definition_94_12_1_Representable
public import stacks_project.Chap96.Lemma_96_19_2

/-!
# Base change of relative Čech complexes along 2-fibre products

A 2-fibre product square of categories fibred in groupoids over `(Sch/S)_fppf`
makes the Lemma 96.19.2 comparison `e⁻¹ K^•(f, F) ⟶ K^•(g, e⁻¹ F)` an
isomorphism of complexes of abelian presheaves.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Functor FiberedCategoryOver.Groupoids Bicategory
open scoped Bicategory Simplicial

noncomputable section

universe u

variable {S : Scheme.{u}} {U X : GroupoidsOver S}

/-- Lemma 96.19.5: if
`V ⟶ U` by `h`, `V ⟶ Y` by `g`, `U ⟶ X` by `f`, and `Y ⟶ X` by `e`
is a 2-fibre product of categories fibred in groupoids over `(Sch/S)_fppf`
and `F` is an abelian presheaf on `X`, then the Lemma 96.19.2 comparison
`e⁻¹ K^•(f, F) ⟶ K^•(g, e⁻¹ F)` is an isomorphism of complexes of abelian
presheaves.

The 2-fibre-product hypothesis is `IsBilimit` of the packed cone
`⟨V, g, h, t.symm⟩` over the cospan `e, f`; equivalently `t.symm` is the
cone cell `g ≫ e ≅ h ≫ f`. -/
@[stacks 06XC]
theorem relativeCechMap_isIso_of_twoFibreProduct {V Y : GroupoidsOver S}
    (f : U ⟶ X) (g : V ⟶ Y) (h : V ⟶ U) (e : Y ⟶ X) (t : h ≫ f ≅ g ≫ e)
    (F : X.totalᵒᵖ ⥤ AddCommGrpCat.{u + 1})
    (h_twoFibre : (⟨V, g, h, t.symm⟩ : PseudoPullbackCone e f).IsBilimit) :
    IsIso (relativeCechMap f g h e t F) :=
  sorry

/-- On the chosen 2-fibre product of `e` and `f` in `GroupoidsOver S`, the
comparison `relativeCechMap` is an isomorphism of complexes of abelian
presheaves. -/
instance relativeCechMap_isIso_twoFibreProduct {Y : GroupoidsOver S}
    (f : U ⟶ X) (e : Y ⟶ X) (F : X.totalᵒᵖ ⥤ AddCommGrpCat.{u + 1}) :
    IsIso (relativeCechMap f
      (TwoFibreProduct.fst.{u + 1, u, u + 1, u} e f)
      (TwoFibreProduct.snd.{u + 1, u, u + 1, u} e f) e
      (TwoFibreProduct.comparisonIso.{u + 1, u, u + 1, u} e f).symm F) :=
  sorry

end
