/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap92.Lemma_92_18_4_Homology
import Mathlib.Tactic.CrossRefAttribute

/-!
# Homology of the cotangent complex of a morphism of ring sheaves

Lemma 92.18.4 identifies the cohomology sheaf `H^i(L(B/A))` with the sheaf associated to
the presheaf of ring-level cotangent cohomology `U ↦ H^i(L(B(U)/A(U)))`.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open HomologicalComplex
open SheafOfModules.RingedSite.CotangentComplex
open SheafOfModules.RingedSite.CotangentComplex.Homology
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

/-- Lemma 92.18.4. Let `C` be a site. Let `A ⟶ B` be a homomorphism of sheaves of rings
on `C`. Then `H^i(L(φ))` is the sheaf associated to the presheaf
`U ↦ H^i(L(B(U)/A(U)))`. -/
@[stacks 08SW]
instance homologyIso {A B : Sheaf J CommRingCat.{u}} (φ : A ⟶ B) (i : ℤ) :
    IsIso (comparison φ i) := sorry
