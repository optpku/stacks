/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.FiniteSupport.Admissible
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.FiniteSupport.Sections
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.FiniteSupport.Presheaf
public import ReasLib.Topology.Opens.RelativeComplement
public import Mathlib.CategoryTheory.Category.Pointed
public import Mathlib.AlgebraicGeometry.Sites.Etale

/-!
# Pointed sections with admissible support

Pointed sections supported on an admissible locally closed subset form a diagram under restriction.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
open TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

variable {X Y : Scheme.{u}}

private theorem pointedHomOfLE_refl {W : Scheme.{u}} (hW : W ⟶ X) [Etale hW]
    (U : W.Opens) : FiniteSupport.homOfLE hW (le_refl U) = 𝟙 _ := by
  apply MorphismProperty.Over.Hom.ext
  exact Scheme.homOfLE_rfl W U

private theorem pointedHomOfLE_comp {W : Scheme.{u}} (hW : W ⟶ X) [Etale hW]
    {U V T : W.Opens} (hUV : U ≤ V) (hVT : V ≤ T) :
    FiniteSupport.homOfLE hW hUV ≫ FiniteSupport.homOfLE hW hVT =
      FiniteSupport.homOfLE hW (hUV.trans hVT) := by
  apply MorphismProperty.Over.Hom.ext
  exact Scheme.homOfLE_homOfLE W hUV hVT

private theorem pointedPreimageHom_naturality (f : X ⟶ Y) [LocallyQuasiFinite f]
    {V' V : Y.Etale} (g : V' ⟶ V) {U T : (baseChangeScheme f V).Opens} (h : U ≤ T) :
    FiniteSupport.homOfLE (baseChangeToSource f V')
        ((FiniteSupport.baseChangeSchemeMap f g).preimage_mono h) ≫
        FiniteSupport.preimageHom f g T =
      FiniteSupport.preimageHom f g U ≫
        FiniteSupport.homOfLE (baseChangeToSource f V) h := by
  apply MorphismProperty.Over.Hom.ext
  change (baseChangeScheme f V').homOfLE
      ((FiniteSupport.baseChangeSchemeMap f g).preimage_mono h) ≫
      FiniteSupport.preimageSchemeHom f g T =
    FiniteSupport.preimageSchemeHom f g U ≫ (baseChangeScheme f V).homOfLE h
  apply (cancel_mono T.ι).1
  have hfac (S : (baseChangeScheme f V).Opens) :
      FiniteSupport.preimageSchemeHom f g S ≫ S.ι =
        (FiniteSupport.baseChangeSchemeMap f g ⁻¹ᵁ S).ι ≫
          FiniteSupport.baseChangeSchemeMap f g := by
    exact IsOpenImmersion.lift_fac S.ι
      ((FiniteSupport.baseChangeSchemeMap f g ⁻¹ᵁ S).ι ≫
        FiniteSupport.baseChangeSchemeMap f g) (by
      rintro _ ⟨x, rfl⟩
      exact ⟨⟨FiniteSupport.baseChangeSchemeMap f g x.1, x.2⟩, rfl⟩)
  simp only [Category.assoc, hfac, Scheme.homOfLE_ι, Scheme.homOfLE_ι_assoc]

private theorem pointedMap_comp (F : Sheaf X.smallEtaleTopology Pointed.{u})
    {U V T : X.Etale} (g : U ⟶ V) (h : V ⟶ T) (s : F.1.obj (op T)) :
    (F.1.map (g ≫ h).op).toFun s =
      (F.1.map g.op).toFun ((F.1.map h.op).toFun s) := by
  rw [op_comp, F.1.map_comp]
  rfl

/-- A section is supported in `Z` when it is distinguished off `Z` in `U`. -/
def IsPointedSectionSupportedIn (f : X ⟶ Y) [LocallyQuasiFinite f]
    (F : Sheaf X.smallEtaleTopology Pointed.{u}) {W : Scheme.{u}} (hW : W ⟶ X) [Etale hW]
    (Z : LocallyCloseds W) (U : W.Opens) (h_subset : (Z : Set W) ⊆ U)
    (h_closed : IsClosed (U.ι ⁻¹' (Z : Set W)))
    (s : (F.1.obj (op (mk (U.ι ≫ hW)))).X) : Prop :=
  (F.1.map (FiniteSupport.homOfLE hW
      (TopologicalSpace.Opens.relativeComplement_le (U := U) (Z := (Z : Set W))
        (by change IsClosed (U.ι ⁻¹' (Z : Set W)); exact h_closed))).op).toFun s =
    (F.1.obj (op (mk (Scheme.Opens.ι (TopologicalSpace.Opens.relativeComplement U (Z : Set W)
      (by change IsClosed (U.ι ⁻¹' (Z : Set W)); exact h_closed)) ≫ hW)))).point

/-- The pointed set of sections supported on an admissible closed subset. -/
def pointedSectionsSupportedIn (f : X ⟶ Y) [LocallyQuasiFinite f]
    (F : Sheaf X.smallEtaleTopology Pointed.{u}) {V : Y.Etale}
    (A : FiniteSupport.Admissible f V) : Pointed.{u} :=
  Pointed.of
    (⟨(F.1.obj (op (mk (A.ambient.ι ≫ baseChangeToSource f V)))).point,
      (F.1.map _).map_point⟩ :
      { s : (F.1.obj (op (mk (A.ambient.ι ≫ baseChangeToSource f V)))).X //
        IsPointedSectionSupportedIn f F (baseChangeToSource f V) A.subset A.ambient
          A.subset_le_ambient A.isClosed_in_ambient s })

/-- Membership in the supported pointed set is precisely the support condition. -/
theorem mem_pointedSectionsSupportedIn_iff (f : X ⟶ Y) [LocallyQuasiFinite f]
    (F : Sheaf X.smallEtaleTopology Pointed.{u}) {V : Y.Etale}
    (A : FiniteSupport.Admissible f V)
    (s : (F.1.obj (op (mk (A.ambient.ι ≫ baseChangeToSource f V)))).X) :
    IsPointedSectionSupportedIn f F (baseChangeToSource f V) A.subset A.ambient
        A.subset_le_ambient A.isClosed_in_ambient s ↔
      (F.1.map (FiniteSupport.homOfLE (baseChangeToSource f V)
          (TopologicalSpace.Opens.relativeComplement_le (U := A.ambient) (Z := (A.subset : Set _))
            (by change IsClosed (A.ambient.ι ⁻¹' (A.subset : Set _)); exact A.isClosed_in_ambient))).op).toFun s =
        (F.1.obj (op (mk (Scheme.Opens.ι (TopologicalSpace.Opens.relativeComplement A.ambient (A.subset : Set _)
            (by change IsClosed (A.ambient.ι ⁻¹' (A.subset : Set _)); exact A.isClosed_in_ambient)) ≫
          baseChangeToSource f V)))).point := Iff.rfl

set_option backward.isDefEq.respectTransparency false in
/-- Restriction of supported pointed sections along an inclusion of supports. -/
def pointedSectionsSupportedInMap (f : X ⟶ Y) [LocallyQuasiFinite f]
    (F : Sheaf X.smallEtaleTopology Pointed.{u}) {V : Y.Etale}
    {A B : FiniteSupport.Admissible f V} (h : A ≤ B) :
    pointedSectionsSupportedIn f F A ⟶ pointedSectionsSupportedIn f F B where
  toFun s := ⟨(F.1.map (FiniteSupport.homOfLE (baseChangeToSource f V) h.2).op).toFun s.1, by
    let CA : (baseChangeScheme f V).Opens :=
      Opens.relativeComplement A.ambient (A.subset : Set _)
        (by change IsClosed (A.ambient.ι ⁻¹' (A.subset : Set _)); exact A.isClosed_in_ambient)
    let CB : (baseChangeScheme f V).Opens :=
      Opens.relativeComplement B.ambient (B.subset : Set _)
        (by change IsClosed (B.ambient.ι ⁻¹' (B.subset : Set _)); exact B.isClosed_in_ambient)
    have hCA : CA ≤ A.ambient := Opens.relativeComplement_le ..
    have hCB : CB ≤ B.ambient := Opens.relativeComplement_le ..
    have hC : CB ≤ CA := fun x hx ↦ ⟨h.2 hx.1, fun hxA ↦ hx.2 (h.1 hxA)⟩
    have he :
        FiniteSupport.homOfLE (baseChangeToSource f V) hCB ≫
            FiniteSupport.homOfLE (baseChangeToSource f V) h.2 =
          FiniteSupport.homOfLE (baseChangeToSource f V) hC ≫
            FiniteSupport.homOfLE (baseChangeToSource f V) hCA := by
      simp only [pointedHomOfLE_comp]
    change (F.1.map (FiniteSupport.homOfLE (baseChangeToSource f V) hCB).op).toFun
        ((F.1.map (FiniteSupport.homOfLE (baseChangeToSource f V) h.2).op).toFun s.1) = _
    rw [← pointedMap_comp F, he, pointedMap_comp F,
      show (F.1.map (FiniteSupport.homOfLE (baseChangeToSource f V) hCA).op).toFun s.1 =
        (F.1.obj (op (mk (CA.ι ≫ baseChangeToSource f V)))).point from s.2]
    exact (F.1.map _).map_point⟩
  map_point := by
    apply Subtype.ext
    exact (F.1.map _).map_point

set_option backward.isDefEq.respectTransparency false in
/-- The diagram of supported pointed sections indexed by admissible supports. -/
def pointedAdmissibleDiagram (f : X ⟶ Y) [LocallyQuasiFinite f]
    (F : Sheaf X.smallEtaleTopology Pointed.{u}) (V : Y.Etale) :
    FiniteSupport.Admissible f V ⥤ Pointed.{u} where
  obj := pointedSectionsSupportedIn f F
  map h := pointedSectionsSupportedInMap f F (leOfHom h)
  map_id A := by
    apply Pointed.Hom.ext
    funext s
    apply Subtype.ext
    change (F.1.map (FiniteSupport.homOfLE (baseChangeToSource f V)
      (le_refl A.ambient)).op).toFun s.1 = s.1
    rw [pointedHomOfLE_refl, op_id, F.1.map_id]
    rfl
  map_comp {A B C} g h := by
    have hg : B.ambient ≤ A.ambient := (leOfHom g).2
    have hh : C.ambient ≤ B.ambient := (leOfHom h).2
    apply Pointed.Hom.ext
    funext s
    apply Subtype.ext
    change (F.1.map (FiniteSupport.homOfLE (baseChangeToSource f V)
        (hh.trans hg)).op).toFun s.1 =
      (F.1.map (FiniteSupport.homOfLE (baseChangeToSource f V) hh).op).toFun
        ((F.1.map (FiniteSupport.homOfLE (baseChangeToSource f V) hg).op).toFun s.1)
    rw [← pointedHomOfLE_comp, pointedMap_comp F]

set_option backward.isDefEq.respectTransparency false in
/-- Restriction of the supported-section diagram under base change in `Y`. -/
def pointedAdmissibleRestriction (f : X ⟶ Y) [LocallyQuasiFinite f]
    (F : Sheaf X.smallEtaleTopology Pointed.{u}) {V' V : Y.Etale} (g : V' ⟶ V) :
    pointedAdmissibleDiagram f F V ⟶
      FiniteSupport.Admissible.pullbackFunctor f g ⋙ pointedAdmissibleDiagram f F V' where
  app A :=
    { toFun := fun s ↦ ⟨(F.1.map (FiniteSupport.preimageHom f g A.ambient).op).toFun s.1, by
        let C : (baseChangeScheme f V).Opens :=
          Opens.relativeComplement A.ambient (A.subset : Set _)
            (by change IsClosed (A.ambient.ι ⁻¹' (A.subset : Set _)); exact A.isClosed_in_ambient)
        have hC : C ≤ A.ambient := Opens.relativeComplement_le ..
        change (F.1.map (FiniteSupport.homOfLE (baseChangeToSource f V')
            ((FiniteSupport.baseChangeSchemeMap f g).preimage_mono hC)).op).toFun
            ((F.1.map (FiniteSupport.preimageHom f g A.ambient).op).toFun s.1) = _
        rw [← pointedMap_comp F, pointedPreimageHom_naturality f g hC, pointedMap_comp F,
          show (F.1.map (FiniteSupport.homOfLE (baseChangeToSource f V) hC).op).toFun s.1 =
            (F.1.obj (op (mk (C.ι ≫ baseChangeToSource f V)))).point from s.2]
        exact (F.1.map _).map_point⟩
      map_point := by
        apply Subtype.ext
        exact (F.1.map _).map_point }
  naturality {A B} h := by
    have hBA : B.ambient ≤ A.ambient := (leOfHom h).2
    apply Pointed.Hom.ext
    funext s
    apply Subtype.ext
    change (F.1.map (FiniteSupport.preimageHom f g B.ambient).op).toFun
        ((F.1.map (FiniteSupport.homOfLE (baseChangeToSource f V) (leOfHom h).2).op).toFun s.1) =
      (F.1.map (FiniteSupport.homOfLE (baseChangeToSource f V')
        ((FiniteSupport.baseChangeSchemeMap f g).preimage_mono (leOfHom h).2)).op).toFun
        ((F.1.map (FiniteSupport.preimageHom f g A.ambient).op).toFun s.1)
    rw [← pointedMap_comp F, ← pointedMap_comp F]
    exact congrArg (fun k ↦ (F.1.map k.op).toFun s.1)
      (pointedPreimageHom_naturality f g hBA).symm

end AlgebraicGeometry.Scheme.Etale

end
