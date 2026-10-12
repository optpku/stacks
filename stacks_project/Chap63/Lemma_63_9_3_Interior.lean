/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting
public import stacks_project.Chap63.Lemma_63_9_3_Compactification

/-! The canonical source-model identification for gammaA and gammaAB. -/

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
      (CompDiagram.ιInterior (Over.mk g) h A.compHG) ≪≫
    pullback.congrHom (CompDiagram.ιInterior_comp_openImmersion (Over.mk g) h A.compHG) rfl

/-- The forward comparison preserves the projection to Y. -/
theorem firstInteriorIso_hom_toBase :
    (firstInteriorIso X g h A).hom ≫ CompDiagram.toBase X (g ≫ h) A.compF =
      CompDiagram.toBase X g A.compFG := by
  let e := pullbackRightPullbackFstIso (openBase X g h A) A.P_bar.obj.right.hom
    (CompDiagram.ιInterior (Over.mk g) h A.compHG)
  let t := pullback.congrHom
    (CompDiagram.ιInterior_comp_openImmersion (Over.mk g) h A.compHG)
    (rfl : A.P_bar.obj.right.hom = A.P_bar.obj.right.hom)
  calc
    _ = e.hom ≫ (t.hom ≫ pullback.fst (Of.ι A.P_g) A.P_bar.obj.right.hom) :=
      Category.assoc _ _ _
    _ = e.hom ≫ pullback.fst
        (CompDiagram.ιInterior (Over.mk g) h A.compHG ≫ openBase X g h A)
        A.P_bar.obj.right.hom :=
      congrArg (fun k ↦ e.hom ≫ k) (pullbackCongrHom_first
        (CompDiagram.ιInterior_comp_openImmersion (Over.mk g) h A.compHG) rfl)
    _ = _ := pullbackRightPullbackFstIso_hom_fst
      (openBase X g h A) A.P_bar.obj.right.hom (CompDiagram.ιInterior (Over.mk g) h A.compHG)

/-- The reverse comparison also preserves the projection to Y. -/
theorem firstInteriorIso_inv_toBase :
    (firstInteriorIso X g h A).inv ≫ CompDiagram.toBase X g A.compFG =
      CompDiagram.toBase X (g ≫ h) A.compF := by
  rw [Iso.inv_comp_eq]
  exact (firstInteriorIso_hom_toBase X g h A).symm

end AlgebraicGeometry.Scheme.Etale.etaleDerivedLowerShriek.AssocDiagram
end
