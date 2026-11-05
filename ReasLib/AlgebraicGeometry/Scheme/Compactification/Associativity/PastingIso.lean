/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Compactification.Associativity.Diagram

/-! Pullback-pasting identification of the first interiors. -/

@[expose] public section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Compactification

noncomputable section
universe u
namespace AlgebraicGeometry.Scheme.Etale.etaleDerivedLowerShriek.AssocDiagram

/-- Equality transport of a pullback cospan preserves its first projection. -/
private theorem pullbackCongrHom_first {C : Type*} [Category C] {P Q R : C}
    {f₁ f₂ : P ⟶ R} {g₁ g₂ : Q ⟶ R} [HasPullback f₁ g₁] [HasPullback f₂ g₂]
    (hf : f₁ = f₂) (hg : g₁ = g₂) :
    (pullback.congrHom hf hg).hom ≫ pullback.fst f₂ g₂ = pullback.fst f₁ g₁ := by
  subst f₂
  subst g₂
  simp [pullback.congrHom, pullback.map]

variable {Y Z T : Scheme.{u}} (X : Over Y) (g : Y ⟶ Z) (h : Z ⟶ T)
  [IsSeparated X.hom] [Scheme.Hom.FiniteType X.hom]
  [IsSeparated g] [Scheme.Hom.FiniteType g]
  [IsSeparated h] [Scheme.Hom.FiniteType h]
  [CompactSpace X.left] [QuasiSeparatedSpace X.left]
  [CompactSpace Y] [QuasiSeparatedSpace Y]
  [CompactSpace Z] [QuasiSeparatedSpace Z]
  [CompactSpace T] [QuasiSeparatedSpace T]
  (A : AssocDiagram X g h)

/-- The two choices of the interior of f are related by actual pullback pasting. -/
def firstInteriorIso : CompDiagram.interior X g A.compFG ≅
    CompDiagram.interior X (g ≫ h) A.compF :=
  pullbackRightPullbackFstIso (openBase X g h A) A.P_bar.obj.right.hom
      (CompDiagram.ιInterior (h_f_separated := inferInstanceAs (IsSeparated g))
      (h_f_finiteType := inferInstanceAs (Scheme.Hom.FiniteType g))
      (h_X_compact := inferInstanceAs (CompactSpace Y))
      (h_X_quasiSeparated := inferInstanceAs (QuasiSeparatedSpace Y)) (Over.mk g) h A.compHG) ≪≫
    pullback.congrHom (CompDiagram.ιInterior_comp_openImmersion (h_f_separated := inferInstanceAs (IsSeparated g))
      (h_f_finiteType := inferInstanceAs (Scheme.Hom.FiniteType g))
      (h_X_compact := inferInstanceAs (CompactSpace Y))
      (h_X_quasiSeparated := inferInstanceAs (QuasiSeparatedSpace Y)) (Over.mk g) h A.compHG) rfl

/-- The forward comparison preserves the projection to Y. -/
theorem firstInteriorIso_hom_toBase :
    (firstInteriorIso X g h A).hom ≫ CompDiagram.toBase X (g ≫ h) A.compF =
      CompDiagram.toBase X g A.compFG := by
  let e := pullbackRightPullbackFstIso (openBase X g h A) A.P_bar.obj.right.hom
    (CompDiagram.ιInterior (h_f_separated := inferInstanceAs (IsSeparated g))
      (h_f_finiteType := inferInstanceAs (Scheme.Hom.FiniteType g))
      (h_X_compact := inferInstanceAs (CompactSpace Y))
      (h_X_quasiSeparated := inferInstanceAs (QuasiSeparatedSpace Y)) (Over.mk g) h A.compHG)
  let t := pullback.congrHom
    (CompDiagram.ιInterior_comp_openImmersion (h_f_separated := inferInstanceAs (IsSeparated g))
      (h_f_finiteType := inferInstanceAs (Scheme.Hom.FiniteType g))
      (h_X_compact := inferInstanceAs (CompactSpace Y))
      (h_X_quasiSeparated := inferInstanceAs (QuasiSeparatedSpace Y)) (Over.mk g) h A.compHG)
    (rfl : A.P_bar.obj.right.hom = A.P_bar.obj.right.hom)
  calc
    _ = e.hom ≫ (t.hom ≫ pullback.fst (Of.ι A.P_g) A.P_bar.obj.right.hom) :=
      Category.assoc _ _ _
    _ = e.hom ≫ pullback.fst
        (CompDiagram.ιInterior (h_f_separated := inferInstanceAs (IsSeparated g))
      (h_f_finiteType := inferInstanceAs (Scheme.Hom.FiniteType g))
      (h_X_compact := inferInstanceAs (CompactSpace Y))
      (h_X_quasiSeparated := inferInstanceAs (QuasiSeparatedSpace Y)) (Over.mk g) h A.compHG ≫ openBase X g h A)
        A.P_bar.obj.right.hom :=
      congrArg (fun k ↦ e.hom ≫ k) (pullbackCongrHom_first
        (CompDiagram.ιInterior_comp_openImmersion (h_f_separated := inferInstanceAs (IsSeparated g))
      (h_f_finiteType := inferInstanceAs (Scheme.Hom.FiniteType g))
      (h_X_compact := inferInstanceAs (CompactSpace Y))
      (h_X_quasiSeparated := inferInstanceAs (QuasiSeparatedSpace Y)) (Over.mk g) h A.compHG) rfl)
    _ = _ := pullbackRightPullbackFstIso_hom_fst
      (openBase X g h A) A.P_bar.obj.right.hom (CompDiagram.ιInterior (h_f_separated := inferInstanceAs (IsSeparated g))
      (h_f_finiteType := inferInstanceAs (Scheme.Hom.FiniteType g))
      (h_X_compact := inferInstanceAs (CompactSpace Y))
      (h_X_quasiSeparated := inferInstanceAs (QuasiSeparatedSpace Y)) (Over.mk g) h A.compHG)

/-- The reverse comparison also preserves the projection to Y. -/
theorem firstInteriorIso_inv_toBase :
    (firstInteriorIso X g h A).inv ≫ CompDiagram.toBase X g A.compFG =
      CompDiagram.toBase X (g ≫ h) A.compF := by
  rw [Iso.inv_comp_eq]
  exact (firstInteriorIso_hom_toBase X g h A).symm

end AlgebraicGeometry.Scheme.Etale.etaleDerivedLowerShriek.AssocDiagram
end

@[expose] public section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Compactification

noncomputable section
universe u
namespace AlgebraicGeometry.Scheme.Etale.etaleDerivedLowerShriek.AssocDiagram

/-- Equality transport of a pullback cospan preserves its second projection. -/
private theorem pullbackCongrHom_second {C : Type*} [Category C] {P Q R : C}
    {f₁ f₂ : P ⟶ R} {g₁ g₂ : Q ⟶ R} [HasPullback f₁ g₁] [HasPullback f₂ g₂]
    (hf : f₁ = f₂) (hg : g₁ = g₂) :
    (pullback.congrHom hf hg).hom ≫ pullback.snd f₂ g₂ = pullback.snd f₁ g₁ := by
  subst f₂
  subst g₂
  simp [pullback.congrHom, pullback.map]

variable {Y Z T : Scheme.{u}} (X : Over Y) (g : Y ⟶ Z) (h : Z ⟶ T)
  [IsSeparated X.hom] [Scheme.Hom.FiniteType X.hom]
  [IsSeparated g] [Scheme.Hom.FiniteType g]
  [IsSeparated h] [Scheme.Hom.FiniteType h]
  [CompactSpace X.left] [QuasiSeparatedSpace X.left]
  [CompactSpace Y] [QuasiSeparatedSpace Y]
  [CompactSpace Z] [QuasiSeparatedSpace Z]
  [CompactSpace T] [QuasiSeparatedSpace T]
  (A : AssocDiagram X g h)

/-- The first-interior comparison preserves the actual projection into the common ambient. -/
theorem firstInteriorIso_hom_openImmersion :
    (firstInteriorIso X g h A).hom ≫ CompDiagram.openImmersion X (g ≫ h) A.compF =
      CompDiagram.openImmersion X g A.compFG ≫ openMid X g h A := by
  let e := pullbackRightPullbackFstIso (openBase X g h A) A.P_bar.obj.right.hom
    (CompDiagram.ιInterior (h_f_separated := inferInstanceAs (IsSeparated g))
      (h_f_finiteType := inferInstanceAs (Scheme.Hom.FiniteType g))
      (h_X_compact := inferInstanceAs (CompactSpace Y))
      (h_X_quasiSeparated := inferInstanceAs (QuasiSeparatedSpace Y)) (Over.mk g) h A.compHG)
  let t := pullback.congrHom
    (CompDiagram.ιInterior_comp_openImmersion (h_f_separated := inferInstanceAs (IsSeparated g))
      (h_f_finiteType := inferInstanceAs (Scheme.Hom.FiniteType g))
      (h_X_compact := inferInstanceAs (CompactSpace Y))
      (h_X_quasiSeparated := inferInstanceAs (QuasiSeparatedSpace Y)) (Over.mk g) h A.compHG)
    (rfl : A.P_bar.obj.right.hom = A.P_bar.obj.right.hom)
  calc
    _ = e.hom ≫ (t.hom ≫ pullback.snd (Of.ι A.P_g) A.P_bar.obj.right.hom) :=
      Category.assoc _ _ _
    _ = e.hom ≫ pullback.snd
        (CompDiagram.ιInterior (h_f_separated := inferInstanceAs (IsSeparated g))
      (h_f_finiteType := inferInstanceAs (Scheme.Hom.FiniteType g))
      (h_X_compact := inferInstanceAs (CompactSpace Y))
      (h_X_quasiSeparated := inferInstanceAs (QuasiSeparatedSpace Y)) (Over.mk g) h A.compHG ≫ openBase X g h A)
        A.P_bar.obj.right.hom :=
      congrArg (fun k ↦ e.hom ≫ k) (pullbackCongrHom_second
        (CompDiagram.ιInterior_comp_openImmersion (h_f_separated := inferInstanceAs (IsSeparated g))
      (h_f_finiteType := inferInstanceAs (Scheme.Hom.FiniteType g))
      (h_X_compact := inferInstanceAs (CompactSpace Y))
      (h_X_quasiSeparated := inferInstanceAs (QuasiSeparatedSpace Y)) (Over.mk g) h A.compHG) rfl)
    _ = _ := pullbackRightPullbackFstIso_hom_snd
      (openBase X g h A) A.P_bar.obj.right.hom (CompDiagram.ιInterior (h_f_separated := inferInstanceAs (IsSeparated g))
      (h_f_finiteType := inferInstanceAs (Scheme.Hom.FiniteType g))
      (h_X_compact := inferInstanceAs (CompactSpace Y))
      (h_X_quasiSeparated := inferInstanceAs (QuasiSeparatedSpace Y)) (Over.mk g) h A.compHG)

/-- The first-interior comparison preserves the given interior X, and the base Y. -/
theorem firstInteriorIso_hom_interior :
    CompDiagram.ιInterior X g A.compFG ≫ (firstInteriorIso X g h A).hom =
      CompDiagram.ιInterior X (g ≫ h) A.compF := by
  apply (cancel_mono (CompDiagram.openImmersion X (g ≫ h) A.compF)).mp
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun k ↦ CompDiagram.ιInterior X g A.compFG ≫ k)
      (firstInteriorIso_hom_openImmersion X g h A)).trans
    ((Category.assoc _ _ _).symm.trans
    ((congrArg (fun k ↦ k ≫ openMid X g h A)
      (CompDiagram.ιInterior_comp_openImmersion X g A.compFG)).trans
    ((ιMid_comp_openMid X g h A).trans
      (CompDiagram.ιInterior_comp_openImmersion X (g ≫ h) A.compF).symm))))

/-- The two f-interiors are isomorphic as fixed-interior compactifications over Y. -/
def firstCompactificationIso :
    CompDiagram.ofInterior X g A.compFG ≅ CompDiagram.ofInterior X (g ≫ h) A.compF :=
  ObjectProperty.isoMk _ (Under.isoMk
    (Over.isoMk (firstInteriorIso X g h A) (firstInteriorIso_hom_toBase X g h A))
    (by
      apply CostructuredArrow.hom_ext
      exact firstInteriorIso_hom_interior X g h A))

/-- Its forward ambient arrow is the actual pullback-pasting comparison. -/
theorem firstCompactificationIso_hom_ambient :
    Of.ambientMap (firstCompactificationIso X g h A).hom =
      (firstInteriorIso X g h A).hom := rfl

/-- Its inverse ambient arrow is the actual inverse pullback-pasting comparison. -/
theorem firstCompactificationIso_inv_ambient :
    Of.ambientMap (firstCompactificationIso X g h A).inv =
      (firstInteriorIso X g h A).inv := rfl

end AlgebraicGeometry.Scheme.Etale.etaleDerivedLowerShriek.AssocDiagram
end

/-! The actual pullback-pasting identification between the A and B+C models. -/

@[expose] public section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Compactification

noncomputable section
universe u
namespace AlgebraicGeometry.Scheme.Etale.etaleDerivedLowerShriek.AssocDiagram

variable {Y Z T : Scheme.{u}} (X : Over Y) (g : Y ⟶ Z) (h : Z ⟶ T)
  [IsSeparated X.hom] [Scheme.Hom.FiniteType X.hom]
  [IsSeparated g] [Scheme.Hom.FiniteType g]
  [IsSeparated h] [Scheme.Hom.FiniteType h]
  [CompactSpace X.left] [QuasiSeparatedSpace X.left]
  [CompactSpace Y] [QuasiSeparatedSpace Y]
  [CompactSpace Z] [QuasiSeparatedSpace Z]
  [CompactSpace T] [QuasiSeparatedSpace T]
  (A : AssocDiagram X g h)

/-- Pasting the two actual pullbacks identifies the ambient of gammaA with that of gammaBC. -/
def midPastingIso : midInterior X g h A ≅
    CompDiagram.interior (Over.mk (X.hom ≫ g)) h A.compH :=
  pullbackLeftPullbackSndIso (Of.ι A.P_h) A.P_g.obj.right.hom A.P_bar.obj.right.hom

/-- Its forward map is the explicit two-projection lift of the nested pullback. -/
theorem midPastingIso_hom : (midPastingIso X g h A).hom = midPasting X g h A := by
  apply pullback.hom_ext
  · exact (pullbackLeftPullbackSndIso_hom_fst
      (Of.ι A.P_h) A.P_g.obj.right.hom A.P_bar.obj.right.hom).trans
      (midPasting_toBase X g h A).symm
  · exact (pullbackLeftPullbackSndIso_hom_snd
      (Of.ι A.P_h) A.P_g.obj.right.hom A.P_bar.obj.right.hom).trans
      (midPasting_open X g h A).symm

/-- The explicit inverse lift has the prescribed first projection. -/
theorem midPastingInv_first :
    midPastingInv X g h A ≫ toMidBase X g h A = toBaseInterior X g h A :=
  pullback.lift_fst (toBaseInterior X g h A)
    (CompDiagram.openImmersion (Over.mk (X.hom ≫ g)) h A.compH) (midPastingInv_fac X g h A)

/-- The explicit inverse lift has the prescribed second projection. -/
theorem midPastingInv_second :
    midPastingInv X g h A ≫ openMid X g h A =
      CompDiagram.openImmersion (Over.mk (X.hom ≫ g)) h A.compH :=
  pullback.lift_snd (toBaseInterior X g h A)
    (CompDiagram.openImmersion (Over.mk (X.hom ≫ g)) h A.compH) (midPastingInv_fac X g h A)

/-- The inner inverse lift has the prescribed projection to Z. -/
theorem toBaseInterior_first :
    toBaseInterior X g h A ≫ CompDiagram.toBase (Over.mk g) h A.compHG =
      CompDiagram.toBase (Over.mk (X.hom ≫ g)) h A.compH :=
  pullback.lift_fst (CompDiagram.toBase (Over.mk (X.hom ≫ g)) h A.compH)
    (CompDiagram.openImmersion (Over.mk (X.hom ≫ g)) h A.compH ≫ A.P_bar.obj.right.hom)
    (toBaseInterior_fac X g h A)

/-- Its inverse is the explicit nested lift, with its specified projections. -/
theorem midPastingIso_inv : (midPastingIso X g h A).inv = midPastingInv X g h A := by
  apply pullback.hom_ext
  · apply pullback.hom_ext
    · calc
        _ = (midPastingIso X g h A).inv ≫ toMidBase X g h A ≫
            CompDiagram.toBase (Over.mk g) h A.compHG := Category.assoc _ _ _
        _ = CompDiagram.toBase (Over.mk (X.hom ≫ g)) h A.compH :=
          pullbackLeftPullbackSndIso_inv_fst
            (Of.ι A.P_h) A.P_g.obj.right.hom A.P_bar.obj.right.hom
        _ = toBaseInterior X g h A ≫ CompDiagram.toBase (Over.mk g) h A.compHG :=
          (toBaseInterior_first X g h A).symm
        _ = _ := (congrArg (fun k ↦ k ≫ CompDiagram.toBase (Over.mk g) h A.compHG)
          (midPastingInv_first X g h A)).symm
    · calc
        _ = (midPastingIso X g h A).inv ≫ toMidBase X g h A ≫ openBase X g h A :=
          Category.assoc _ _ _
        _ = CompDiagram.openImmersion (Over.mk (X.hom ≫ g)) h A.compH ≫
            A.P_bar.obj.right.hom :=
          pullbackLeftPullbackSndIso_inv_fst_snd
            (Of.ι A.P_h) A.P_g.obj.right.hom A.P_bar.obj.right.hom
        _ = toBaseInterior X g h A ≫ openBase X g h A := (midPastingInv_fac X g h A).symm
        _ = _ := (congrArg (fun k ↦ k ≫ openBase X g h A) (midPastingInv_first X g h A)).symm
  · exact (pullbackLeftPullbackSndIso_inv_snd_snd
      (Of.ι A.P_h) A.P_g.obj.right.hom A.P_bar.obj.right.hom).trans
      (midPastingInv_second X g h A).symm

/-- The forward and inverse lifts are actual inverse morphisms. -/
theorem midPasting_comp_inv : midPasting X g h A ≫ midPastingInv X g h A = 𝟙 _ := by
  rw [← midPastingIso_hom X g h A, ← midPastingIso_inv X g h A]
  exact (midPastingIso X g h A).hom_inv_id

/-- The reverse composite is also the identity. -/
theorem midPasting_inv_comp : midPastingInv X g h A ≫ midPasting X g h A = 𝟙 _ := by
  rw [← midPastingIso_hom X g h A, ← midPastingIso_inv X g h A]
  exact (midPastingIso X g h A).inv_hom_id

/-- The actual A-composite and B+C-interior compactifications are canonically isomorphic. -/
def ofCompositeFG_iso_ofInteriorH :
    CompDiagram.ofComposite X g A.compFG ≅
      CompDiagram.ofInterior (h_f_separated := inferInstanceAs (IsSeparated (X.hom ≫ g)))
      (h_f_finiteType := inferInstanceAs (Scheme.Hom.FiniteType (X.hom ≫ g)))
      (h_X_compact := inferInstanceAs (CompactSpace X.left))
      (h_X_quasiSeparated := inferInstanceAs (QuasiSeparatedSpace X.left)) (Over.mk (X.hom ≫ g)) h A.compH where
  hom := ofCompositeFG_hom_ofInteriorH X g h A
  inv := ofInteriorH_hom_ofCompositeFG X g h A
  hom_inv_id := by
    apply InducedCategory.hom_ext
    apply StructuredArrow.hom_ext
    apply CostructuredArrow.hom_ext
    change (𝟙 _ ≫ midPasting X g h A ≫ 𝟙 _) ≫
      (𝟙 _ ≫ midPastingInv X g h A ≫ 𝟙 _) = 𝟙 _
    simpa only [Category.id_comp, Category.comp_id] using midPasting_comp_inv X g h A
  inv_hom_id := by
    apply InducedCategory.hom_ext
    apply StructuredArrow.hom_ext
    apply CostructuredArrow.hom_ext
    change (𝟙 _ ≫ midPastingInv X g h A ≫ 𝟙 _) ≫
      (𝟙 _ ≫ midPasting X g h A ≫ 𝟙 _) = 𝟙 _
    simpa only [Category.id_comp, Category.comp_id] using midPasting_inv_comp X g h A

end AlgebraicGeometry.Scheme.Etale.etaleDerivedLowerShriek.AssocDiagram
end
