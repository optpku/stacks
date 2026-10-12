/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FinitePresentation

/-!
# Cancellation for finite presentation

Local finite presentation and finite presentation of a composite descend to its left factor under
the corresponding finiteness and separation hypotheses on the right factor.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- If `f ≫ g` is locally of finite presentation and `g` is locally of finite type, then `f` is
locally of finite presentation. -/
theorem LocallyOfFinitePresentation.of_comp
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [LocallyOfFinitePresentation (f ≫ g)] [LocallyOfFiniteType g] :
    LocallyOfFinitePresentation f := by
  let h : LocallyOfFinitePresentation (f ≫ g) := inferInstance
  wlog hZ : IsAffine Z generalizing X Y Z
  · rw [IsZariskiLocalAtTarget.iff_of_iSup_eq_top
      (P := @LocallyOfFinitePresentation) _
      (g.iSup_preimage_eq_top (iSup_affineOpens_eq_top Z))]
    intro U
    have H := IsZariskiLocalAtTarget.restrict h U.1
    rw [morphismRestrict_comp] at H
    have hg' : LocallyOfFiniteType (g ∣_ U.1) :=
      IsZariskiLocalAtTarget.restrict (show LocallyOfFiniteType g from inferInstance) U.1
    exact @this _ _ _ (f ∣_ (g ⁻¹ᵁ U.1)) (g ∣_ U.1) H hg' inferInstance
  wlog hY : IsAffine Y generalizing X Y
  · rw [IsZariskiLocalAtTarget.iff_of_iSup_eq_top
      (P := @LocallyOfFinitePresentation) _ (iSup_affineOpens_eq_top Y)]
    intro U
    have H := HasRingHomProperty.comp_of_isOpenImmersion
      @LocallyOfFinitePresentation (f ⁻¹ᵁ U.1).ι (f ≫ g) h
    rw [← morphismRestrict_ι_assoc] at H
    have hi : LocallyOfFiniteType U.1.ι :=
      @locallyOfFiniteType_of_isOpenImmersion _ _ U.1.ι U.1.instIsOpenImmersionι
    have hg' : LocallyOfFiniteType (U.1.ι ≫ g) :=
      @locallyOfFiniteType_comp _ _ _ U.1.ι g hi inferInstance
    exact @this _ _ (f ∣_ U.1) (U.1.ι ≫ g) H hg' inferInstance
  wlog hX : IsAffine X generalizing X
  · rw [IsZariskiLocalAtSource.iff_of_iSup_eq_top
      (P := @LocallyOfFinitePresentation) _ (iSup_affineOpens_eq_top X)]
    intro U
    have H := HasRingHomProperty.comp_of_isOpenImmersion
      @LocallyOfFinitePresentation U.1.ι (f ≫ g) h
    rw [← Category.assoc] at H
    exact @this _ (U.1.ι ≫ f) H inferInstance
  rw [HasRingHomProperty.iff_of_isAffine
      (P := @LocallyOfFinitePresentation)] at h ⊢
  have hg : (g.appTop).hom.FiniteType :=
    HasRingHomProperty.appTop @LocallyOfFiniteType g inferInstance
  exact h.of_comp_finiteType (g.appTop).hom hg

namespace Scheme.Hom.FinitePresentation

/-- If `f ≫ g` is of finite presentation, `g` is locally of finite type, and `g` is
quasi-separated, then `f` is of finite presentation. -/
theorem of_comp
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [FinitePresentation (f ≫ g)] [LocallyOfFiniteType g] [QuasiSeparated g] :
    FinitePresentation f := sorry

/-- If `f ≫ g` is of finite presentation, `g` is locally of finite type, and `Y` is
quasi-separated, then `f` is of finite presentation. -/
theorem of_comp_of_quasiSeparatedSpace
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [FinitePresentation (f ≫ g)] [LocallyOfFiniteType g] [QuasiSeparatedSpace Y] :
    FinitePresentation f := sorry

end Scheme.Hom.FinitePresentation
end AlgebraicGeometry
