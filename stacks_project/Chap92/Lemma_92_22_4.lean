module

public import stacks_project.Chap92.Lemma_92_22_4_NaiveCotangent
public import stacks_project.Chap92.Lemma_92_18_10_Comparison
import Mathlib.Tactic.CrossRefAttribute

/-!
# Comparison of the cotangent complex of a morphism of ringed topoi with the naive cotangent complex

Lemma 92.22.4 records the canonical cochain map `L[f] ⟶ NL[f]` identifying the naive
cotangent complex with the good truncation `τ_{≥ -1} L[f]`.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Sheaf
open HomologicalComplex
open SheafOfModules.RingedSite
open scoped RingedSite.ToposHom
open scoped SheafOfModules.RingedSite

noncomputable section

universe u

namespace RingedSite.ToposHom

variable {C D : Type u} [Category.{u} C] [Category.{u} D]
variable {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}
variable [JC.HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
variable [JD.HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
variable [JC.HasSheafCompose (forget RingCat.{u})]
variable [JD.HasSheafCompose (forget RingCat.{u})]
variable [JC.HasSheafCompose (CategoryTheory.forget CommRingCat.{u})]
variable [HasWeakSheafify JC CommRingCat.{u}]
variable [HasWeakSheafify JC AddCommGrpCat.{u}]
variable [JC.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [HasColimitsOfShape (Discrete WalkingPair) CommRingCat.{u}]
variable {OC : Sheaf JC CommRingCat.{u}} {OD : Sheaf JD CommRingCat.{u}}

/-- Lemma 92.22.4 (1). Let `f : (Sh(C), O) ⟶ (Sh(B), O_B)` be a morphism of
ringed topoi. There is a canonical cochain map `L[f] ⟶ NL[f]`. -/
@[stacks 08V2]
def toNaive
    (f : ToposHom (RingedSite.ofCommRingSheaf JC OC)
      (RingedSite.ofCommRingSheaf JD OD)) :
    L[f] ⟶ NL[f] :=
  CotangentComplex.toNaive (inverseImageStructureSheaf f) (Under.mk (structureSheafMap f))

/-- Lemma 92.22.4 (2). The canonical map identifies `NL[f]` with the truncation
`τ_{≥ -1} L[f]`. -/
@[stacks 08V2]
instance toNaive_truncGE_quasiIso
    (f : ToposHom (RingedSite.ofCommRingSheaf JC OC)
      (RingedSite.ofCommRingSheaf JD OD)) :
    QuasiIso (CochainComplex.truncGEMap (toNaive f) (-1)) :=
  sorry

/-- Unfolding of the source-facing comparison recovers the sheaf-level `toNaive`
of `structureSheafMap f`. -/
theorem toNaive_eq
    (f : ToposHom (RingedSite.ofCommRingSheaf JC OC)
      (RingedSite.ofCommRingSheaf JD OD)) :
    toNaive f =
      CotangentComplex.toNaive (inverseImageStructureSheaf f)
        (Under.mk (structureSheafMap f)) :=
  sorry

/-- Degree `0` of the source-facing `toNaive` is the identification of
`Ω_{P₀/A} ⊗_{P₀} B`. -/
theorem toNaive_f_zero
    (f : ToposHom (RingedSite.ofCommRingSheaf JC OC)
      (RingedSite.ofCommRingSheaf JD OD)) :
    (toNaive f).f 0 =
      (CotangentComplex.objXIso (inverseImageStructureSheaf f)
          (Under.mk (structureSheafMap f)) 0).hom ≫
        CotangentComplex.selfDifferentials (inverseImageStructureSheaf f)
          (Under.mk (structureSheafMap f)) :=
  sorry

/-- Degree `-1` of the source-facing `toNaive` is the face-difference map `toConormal`. -/
theorem toNaive_f_negOne
    (f : ToposHom (RingedSite.ofCommRingSheaf JC OC)
      (RingedSite.ofCommRingSheaf JD OD)) :
    (toNaive f).f (-1) =
      (CotangentComplex.objXIso (inverseImageStructureSheaf f)
          (Under.mk (structureSheafMap f)) 1).hom ≫
        CotangentComplex.toConormal (inverseImageStructureSheaf f)
          (Under.mk (structureSheafMap f)) :=
  sorry

end RingedSite.ToposHom

