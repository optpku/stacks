/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap91.«91_13_1_2_Diagram»

/-!
# Fitting morphisms of a relative first-order thickening diagram

After identifying underlying topoi, a fitting map is a morphism of ring sheaves
`𝒪'₁ ⟶ 𝒪'₂` filling the omitted edge of a relative first-order thickening diagram,
compatibly with the given `g`-map of kernel ideals.
-/

@[expose] public section

open CategoryTheory
open SheafOfModules.RingedSite

noncomputable section

universe u v

namespace SheafOfModules.RingedSite.FirstOrderThickening

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
variable [J.HasSheafCompose (forget₂ RingCat.{max u v} AddCommGrpCat.{max u v})]
variable [HasWeakSheafify J CommRingCat.{max u v}]
variable [J.WEqualsLocallyBijective CommRingCat.{max u v}]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable {O1 O1' OB1 OB1' O2 O2' OB2 OB2' : Sheaf J CommRingCat.{max u v}}
variable {πO1 : O1' ⟶ O1} {πB1 : OB1' ⟶ OB1}
variable {πO2 : O2' ⟶ O2} {πB2 : OB2' ⟶ OB2}
variable [IsFirstOrderThickening πO1] [IsFirstOrderThickening πB1]
variable [IsFirstOrderThickening πO2] [IsFirstOrderThickening πB2]

/-- A morphism `𝒪'₁ ⟶ 𝒪'₂` fitting into the identified-topoi form of 91.13.1.1
compatibly with the given `g`-map `ν`. -/
structure FittingMap (D : RelativeDiagram πO1 πB1 πO2 πB2) where
  /-- The filling morphism of ring sheaves `𝒪'₁ ⟶ 𝒪'₂`. -/
  hom : O1' ⟶ O2'
  /-- The filling morphism is compatible with the thickenings `π_{𝒪ⱼ}`. -/
  comm_π : hom ≫ πO2 = πO1 ≫ D.g
  /-- The filling morphism is compatible with the structure maps `f'ⱼ`. -/
  comm_f' : D.t' ≫ D.f2' = D.f1' ≫ hom
  /-- The filling morphism induces the given `g`-map on kernel ideals. -/
  induces : inducedKernelMap πO1 D.g πO2 hom comm_π = D.ν

namespace FittingMap

variable {D : RelativeDiagram πO1 πB1 πO2 πB2}

/-- Assemble a fitting map from a morphism `𝒪'₁ ⟶ 𝒪'₂` and the three compatibility
conditions. -/
def of (hom : O1' ⟶ O2') (comm_π : hom ≫ πO2 = πO1 ≫ D.g)
    (comm_f' : D.t' ≫ D.f2' = D.f1' ≫ hom)
    (induces : inducedKernelMap πO1 D.g πO2 hom comm_π = D.ν) :
    FittingMap D where
  hom := hom
  comm_π := comm_π
  comm_f' := comm_f'
  induces := induces

/-- A fitting map makes the two present faces through it commute and induces `ν` on
kernels. -/
theorem spec (φ : FittingMap D) :
    φ.hom ≫ πO2 = πO1 ≫ D.g ∧ D.t' ≫ D.f2' = D.f1' ≫ φ.hom ∧
      inducedKernelMap πO1 D.g πO2 φ.hom φ.comm_π = D.ν := sorry

/-- A morphism `𝒪'₁ ⟶ 𝒪'₂` underlies a fitting map if and only if it fits the relative
diagram in the sense of `RelativeDiagram.Fits`. -/
theorem fits_iff (hom : O1' ⟶ O2') :
    (∃ φ : FittingMap D, φ.hom = hom) ↔ RelativeDiagram.Fits D hom := sorry

end FittingMap

end SheafOfModules.RingedSite.FirstOrderThickening
