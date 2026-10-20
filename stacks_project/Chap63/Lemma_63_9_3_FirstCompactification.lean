/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap63.Lemma_63_9_3_Interior

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
    (CompDiagram.ιInterior (Over.mk g) h A.compHG)
  let t := pullback.congrHom
    (CompDiagram.ιInterior_comp_openImmersion (Over.mk g) h A.compHG)
    (rfl : A.P_bar.obj.right.hom = A.P_bar.obj.right.hom)
  calc
    _ = e.hom ≫ (t.hom ≫ pullback.snd (Of.ι A.P_g) A.P_bar.obj.right.hom) :=
      Category.assoc _ _ _
    _ = e.hom ≫ pullback.snd
        (CompDiagram.ιInterior (Over.mk g) h A.compHG ≫ openBase X g h A)
        A.P_bar.obj.right.hom :=
      congrArg (fun k ↦ e.hom ≫ k) (pullbackCongrHom_second
        (CompDiagram.ιInterior_comp_openImmersion (Over.mk g) h A.compHG) rfl)
    _ = _ := pullbackRightPullbackFstIso_hom_snd
      (openBase X g h A) A.P_bar.obj.right.hom (CompDiagram.ιInterior (Over.mk g) h A.compHG)

/-- The first-interior comparison preserves the given interior X, not only the base Y. -/
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
