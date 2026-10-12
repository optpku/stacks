/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap92.Definition_92_22_1_Morphism
public import stacks_project.Chap92.Lemma_92_18_6_HomologyZero
import Mathlib.Tactic.CrossRefAttribute

/-!
# Degree-zero homology of the cotangent complex of a morphism of ringed topoi

Lemma 92.22.2 identifies `H^0(L[f])` with the sheaf of relative differentials
`Ω(structureSheafMap f)` for a morphism of ringed topoi.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Sheaf
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

/-- Lemma 92.22.2. Let `f : (Sh(C), O) ⟶ (Sh(B), O_B)` be a morphism of ringed
topoi. Then `H^0(L[f]) = Ω(structureSheafMap f)`. -/
@[stacks 08V0]
abbrev homologyZeroIso
    (f : ToposHom (RingedSite.ofCommRingSheaf JC OC)
      (RingedSite.ofCommRingSheaf JD OD)) :
    L[f].homology 0 ≅ Ω(structureSheafMap f) :=
  CotangentComplex.homologyZeroIso (structureSheafMap f)

/-- The forward morphism of `homologyZeroIso` is the canonical comparison
`homologyZeroMap` of `structureSheafMap f`. -/
theorem homologyZeroIso_hom
    (f : ToposHom (RingedSite.ofCommRingSheaf JC OC)
      (RingedSite.ofCommRingSheaf JD OD)) :
    (homologyZeroIso f).hom =
      CotangentComplex.homologyZeroMap (structureSheafMap f) :=
  sorry

end RingedSite.ToposHom
