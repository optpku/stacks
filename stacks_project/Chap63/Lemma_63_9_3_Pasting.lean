module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting
public import stacks_project.Chap63.Lemma_63_9_3_Compactification

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

/-- Its forward map is the explicit two-projection lift already used by the source construction. -/
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

/-- Its inverse is the explicit nested lift, not an inverse selected from a deferred IsIso proof. -/
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
      CompDiagram.ofInterior (Over.mk (X.hom ≫ g)) h A.compH where
  hom := ofCompositeFG_hom_ofInteriorH X g h A
  inv := ofInteriorH_hom_ofCompositeFG X g h A
  hom_inv_id := by
    apply InducedCategory.hom_ext
    apply StructuredArrow.hom_ext
    apply CostructuredArrow.hom_ext
    simpa [ofCompositeFG_hom_ofInteriorH, ofInteriorH_hom_ofCompositeFG,
      ofCompositeFG_left, ofInteriorH_left] using midPasting_comp_inv X g h A
  inv_hom_id := by
    apply InducedCategory.hom_ext
    apply StructuredArrow.hom_ext
    apply CostructuredArrow.hom_ext
    simpa [ofCompositeFG_hom_ofInteriorH, ofInteriorH_hom_ofCompositeFG,
      ofCompositeFG_left, ofInteriorH_left] using midPasting_inv_comp X g h A

end AlgebraicGeometry.Scheme.Etale.etaleDerivedLowerShriek.AssocDiagram
end
