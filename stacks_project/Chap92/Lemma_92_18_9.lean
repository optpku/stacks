/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap92.Lemma_92_18_9_Comparison
import Mathlib.Tactic.CrossRefAttribute

/-!
# Stalks of the sheaf cotangent complex

Lemma 92.18.9 identifies the stalk of `L(φ)` at a site point `p` with the
algebra cotangent complex of the stalk map `A_p ⟶ B_p`.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.GrothendieckTopology
open HomologicalComplex
open SheafOfModules.RingedSite.CotangentComplex
open scoped SheafOfModules.RingedSite.CotangentComplex

noncomputable section

universe u

variable {C : Type u} [Category.{u} C] [LocallySmall.{u} C]
variable {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
variable [J.HasSheafCompose (CategoryTheory.forget CommRingCat.{u})]
variable [HasWeakSheafify J CommRingCat.{u}]
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [HasColimitsOfShape (Discrete WalkingPair) CommRingCat.{u}]

/-- Lemma 92.18.9. Let `C` be a site. Let `φ : A ⟶ B` be a homomorphism of
sheaves of rings on `C`. If `p` is a point of `C`, then `(L(φ))_p ≅ L(B_p / A_p)`,
as a canonical isomorphism of cochain complexes of modules over `B_p`. -/
@[stacks 08T0]
abbrev stalkIso {A B : Sheaf J CommRingCat.{u}} (φ : A ⟶ B) (p : Point.{u} J) :
    Stalk.source φ p ≅ Stalk.target φ p :=
  Stalk.iso φ p

/-- In cohomological degree `-n`, the stalk identification compares the corresponding
simplicial tensor terms. -/
theorem stalkIso_hom_f {A B : Sheaf J CommRingCat.{u}} (φ : A ⟶ B) (p : Point.{u} J)
    (n : ℕ) :
    (stalkIso φ p).hom.f (-n) =
      (Stalk.sourceXIso φ p n).hom ≫
        (Stalk.termIso φ p n).hom ≫ (Stalk.targetXIso φ p n).inv :=
  sorry

end
end
