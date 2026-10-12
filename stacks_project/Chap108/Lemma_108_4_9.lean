/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap67.Definition_67_4_2_Separation
public import stacks_project.Chap108.Lemma_108_4_5_OpenImmersion
public import stacks_project.Chap108.Lemma_108_4_6_ClosedImmersion
public import stacks_project.Chap108.Lemma_108_4_9_ModuleSheaves
public import stacks_project.Chap108.Lemma_108_4_9_DenseModuleSheaves
public import stacks_project.Chap108.Lemma_108_4_9_SchemeEtaleModules
public import stacks_project.Chap108.Lemma_108_4_9_Atlas
public import stacks_project.Chap108.Lemma_108_4_9_AtlasPullback
public import stacks_project.Chap108.Lemma_108_4_9_AtlasCoverSurjectivity
public import stacks_project.Chap108.Lemma_108_4_9_AtlasSiteCover
public import stacks_project.Chap108.Lemma_108_4_9_DenseSiteComposition
public import stacks_project.Chap108.Lemma_108_4_9_AffineBasis
public import stacks_project.Chap108.Lemma_108_4_9_SmallHypercover
public import stacks_project.Chap108.Lemma_108_4_9_DenseSheafification
public import stacks_project.Chap108.Lemma_108_4_9_ModulesGrothendieck
public import stacks_project.Chap108.Lemma_108_4_9_InjectiveResolution
public import stacks_project.Chap108.Lemma_108_4_9_SliceHomSmall
public import stacks_project.Chap108.Lemma_108_4_9_LocalHomCarrier
public import stacks_project.Chap108.Lemma_108_4_9_StructureSheafResolution
public import stacks_project.Chap108.Lemma_108_4_9_InternalHom
public import stacks_project.Chap108.Lemma_108_4_9_InternalHomClosed
public import stacks_project.Chap108.Lemma_108_4_9_TensorPower
public import stacks_project.Chap108.Situation_108_4_7_Numerical_invariants_Substack

/-!
# Lemma 108.4.9

For `f : X ⟶ B` separated of finite presentation, a finite list of perfect
objects of `D(𝒪_X)`, and any numerical function `P` on `ℤ^{⊕ r}`, the
numerical substack `Coh^P_{X/B}` of Situation 108.4.7 is an open and closed
substack of `Coh_{X/B}`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.CohStack
open AlgebraicGeometry.AlgebraicSpace.Modules
open AlgebraicGeometry.AlgebraicSpace.ModuleDerived
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.CohStack

variable {S : Scheme.{u}} {X B : AlgebraicSpace S}

/-- Lemma 108.4.9 (1): for `f : X ⟶ B` separated of finite presentation, perfect
objects `E 0, …, E (r-1)` of `D(𝒪_X)`, and any `P : tensorPowerIndex r → ℤ`,
the inclusion `Numerical.ι` of the numerical substack associated to the family
`(n) ↦ ⨂ᵢ E i ^{⊗ n i}` is an open immersion. -/
@[stacks 0DNE]
instance instOpenImmersion_ι_tensorPower (f : X ⟶ B)
    [FinitePresentation f] [Separated f] {r : ℕ}
    (E : Fin r → ModuleDerived X)
    (hE : ∀ i, ModuleDerived.IsPerfect (E i))
    (P : tensorPowerIndex r → ℤ) :
    Hom.OpenImmersion
      (Numerical.ι f (tensorPowerFamily E) P
        (fun n ↦ isPerfect_tensorPowerFamily E hE n)) :=
  sorry

/-- Lemma 108.4.9 (2): for `f : X ⟶ B` separated of finite presentation, perfect
objects `E 0, …, E (r-1)` of `D(𝒪_X)`, and any `P : tensorPowerIndex r → ℤ`,
the inclusion `Numerical.ι` of the numerical substack associated to the family
`(n) ↦ ⨂ᵢ E i ^{⊗ n i}` is a closed immersion. -/
@[stacks 0DNE]
instance instClosedImmersion_ι_tensorPower (f : X ⟶ B)
    [FinitePresentation f] [Separated f] {r : ℕ}
    (E : Fin r → ModuleDerived X)
    (hE : ∀ i, ModuleDerived.IsPerfect (E i))
    (P : tensorPowerIndex r → ℤ) :
    Hom.ClosedImmersion
      (Numerical.ι f (tensorPowerFamily E) P
        (fun n ↦ isPerfect_tensorPowerFamily E hE n)) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.CohStack
