/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap85.Lemma_85_34_4_DerivedQCoh
public import stacks_project.Chap85.Lemma_85_34_4_Equivalence

/-!
# Lemma 85.34.4

Let `S` be a scheme, `X` an algebraic space over `S`, and `U` a simplicial
algebraic space over `S`, with augmentation `a : U ⟶ X`. If `a` is an fppf
hypercovering of `X`, then `QCoh(𝒪_U)` is a weak Serre subcategory of
`Mod(𝒪_U)`, and `a^* : D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_U)` is an equivalence with
quasi-inverse `Ra_*`. Here `a` is the Section 85.32 spaces-étale augmentation
of ringed topoi.
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry CategoryTheory.ObjectProperty
open AlgebraicGeometry.AlgebraicSpace.Simplicial
open Functor
open scoped Simplicial

noncomputable section

namespace AlgebraicGeometry.AlgebraicSpace.Simplicial

variable {S : Scheme.{u}} {X : AlgebraicSpace S}
variable {U : SimplicialObject (AlgebraicSpace S)}
variable (a : U ⟶ (const SimplexCategoryᵒᵖ).obj X)

/-- Lemma 85.34.4 (1): Let `S` be a scheme. Let `X` be an algebraic space over `S`.
Let `U` be a simplicial algebraic space over `S`. Let `a : U ⟶ X` be an
augmentation. If `a : U ⟶ X` is an fppf hypercovering of `X`, then
`QCoh(𝒪_U)` is a weak Serre subcategory of `Mod(𝒪_U)`. Here `a` is the
Section 85.32 spaces-étale augmentation, and `QCoh(𝒪_U)` (resp. `Mod(𝒪_U)`)
is the category of quasi-coherent modules (resp. all modules) on
`etaleTotalRingedSite U` at coefficient universe `u + 1`. -/
@[stacks 0DHF]
instance quasiCoherent_isWeakSerreClass (ha : IsFppfHypercovering a) :
    let _ := ha
    (quasiCoherentProperty U).IsWeakSerreClass :=
  sorry

/-- Lemma 85.34.4 (2): Let `S` be a scheme. Let `X` be an algebraic space over `S`.
Let `U` be a simplicial algebraic space over `S`. Let `a : U ⟶ X` be an
augmentation. If `a : U ⟶ X` is an fppf hypercovering of `X`, then
`a^* : D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_U)` is an equivalence of categories with
quasi-inverse `Ra_*`. Here `a : Sh(U_étale) ⟶ Sh(X_étale)` is the Section 85.32
spaces-étale augmentation `spacesEtaleAugmentationHom`. -/
@[stacks 0DHF]
def derivedQCohEquivalence (ha : IsFppfHypercovering a) :
    spacesDerivedQCoh X ≌ DerivedQCoh U :=
  derivedQCohDescent a ha

/-- The forward functor of `derivedQCohEquivalence` is `a^*` restricted to
`D_QCoh`. -/
theorem derivedQCohEquivalence_functor (ha : IsFppfHypercovering a) :
    (derivedQCohEquivalence a ha).functor = DerivedQCoh.pullback a :=
  sorry

/-- The inverse functor of `derivedQCohEquivalence` is `Ra_*` on `D_QCoh`. -/
theorem derivedQCohEquivalence_inverse (ha : IsFppfHypercovering a) :
    (derivedQCohEquivalence a ha).inverse = DerivedQCoh.pushforward a ha :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Simplicial

end
