module

public import stacks_project.Chap92.Lemma_92_18_6_HomologyZero
import Mathlib.Tactic.CrossRefAttribute

/-!
# Degree-zero homology of the cotangent complex of a morphism of ring sheaves

Lemma 92.18.6 identifies the cohomology sheaf `H^0(L(φ))` with the sheaf of relative
differentials `Ω(φ)`.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open SheafOfModules.RingedSite
open scoped SheafOfModules.RingedSite
open scoped SheafOfModules.RingedSite.CotangentComplex

noncomputable section

universe u

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
variable [J.HasSheafCompose (CategoryTheory.forget CommRingCat.{u})]
variable [HasWeakSheafify J CommRingCat.{u}]
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [HasColimitsOfShape (Discrete WalkingPair) CommRingCat.{u}]

/-- Lemma 92.18.6. Let `C` be a site. Let `A ⟶ B` be a homomorphism of sheaves of rings
on `C`. Then `H^0(L(φ)) = Ω(φ)`. -/
@[stacks 08UR]
abbrev homologyZeroIso {A B : Sheaf J CommRingCat.{u}} (φ : A ⟶ B) :
    L(φ).homology 0 ≅ Ω(φ) :=
  CotangentComplex.homologyZeroIso φ

/-- The forward morphism of `homologyZeroIso` is the canonical comparison `homologyZeroMap`. -/
theorem homologyZeroIso_hom {A B : Sheaf J CommRingCat.{u}} (φ : A ⟶ B) :
    (homologyZeroIso φ).hom = CotangentComplex.homologyZeroMap φ :=
  sorry
