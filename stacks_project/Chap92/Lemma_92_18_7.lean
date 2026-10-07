module

public import stacks_project.Chap92.Lemma_92_18_7_Functoriality
public import stacks_project.Chap92.Lemma_92_18_7_Product
import Mathlib.Tactic.CrossRefAttribute

/-!
# Product of cotangent complexes of sheaves of rings

The comparison `L(B ⨯ B' / A) ⟶ L(B/A) ⊕ L(B'/A)` is an isomorphism in `D(B ⨯ B')`.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open SheafOfModules.RingedSite.CotangentComplex
open scoped SheafOfModules.RingedSite.CotangentComplex

universe u

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
variable [J.HasSheafCompose (CategoryTheory.forget CommRingCat.{u})]
variable [HasWeakSheafify J CommRingCat.{u}]
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [HasColimitsOfShape (Discrete WalkingPair) CommRingCat.{u}]
variable [UnivLE.{u, u}]

/-- Lemma 92.18.7. Let `C` be a site. Let `A ⟶ B` and `A ⟶ B'` be homomorphisms of
sheaves of rings on `C`. Then `L(B ⨯ B' / A) ⟶ L(B/A) ⊕ L(B'/A)` is an isomorphism
in `D(B ⨯ B')`. -/
@[stacks 08SY]
instance prodMap_isIso {A B B' : Sheaf J CommRingCat.{u}} (φ : A ⟶ B) (ψ : A ⟶ B') :
    IsIso (prodMap φ ψ) :=
  sorry
