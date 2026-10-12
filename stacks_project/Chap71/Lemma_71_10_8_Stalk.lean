/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap65.Lemma_65_12_4_Immersion
public import stacks_project.Chap66.Lemma_66_5_5_PointsTopology
public import stacks_project.Chap67.Lemma_67_49_1_FiniteComponents
public import stacks_project.Chap68.Lemma_68_4_3_Fibre
public import stacks_project.Chap68.Lemma_68_22_3_SpecStalk
public import stacks_project.Chap71.Lemma_71_6_11_WeaklyAssociated

/-!
# Canonical stalk maps at codimension-zero points

If an algebraic space has finitely many irreducible components on compact opens and every
codimension-zero point is represented by a monomorphism from the spectrum of a field, then each
point of `X^0` lies on an open-immersion chart. The canonical map
`j_η : Spec(𝒪_{X,η}) ⟶ X` is `fromSpecStalk` of a chosen such chart.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- An open-immersion chart of an algebraic space, given by a scheme over `S`, a morphism into
`X`, and a point of that scheme. -/
structure OpenImmersionChart {S : Scheme.{u}} (X : AlgebraicSpace S) where
  /-- The source scheme over `S`. -/
  U : Over S
  /-- The morphism `ofOver U ⟶ X`. -/
  ι : ofOver U ⟶ X
  /-- A point of the source scheme. -/
  u : U.left

/-- If every weakly associated point of `X` has codimension `0`, `X` satisfies Morphisms of
Spaces Lemma 67.49.1, and every codimension-`0` point is represented by a monomorphism
`Spec(k) ⟶ X`, then each point of `X^0` lies on an open-immersion chart from a scheme. -/
theorem exists_isOpenImmersion_chart_of_mem_codimZero {S : Scheme.{u}} {X : AlgebraicSpace S}
    [HasFiniteIrreducibleComponentsOnCompactOpens X]
    (hweak : X.weakAss ⊆ codimZeroPoints X)
    (hmono : ∀ η ∈ codimZeroPoints X, existsMonoFieldValuedPoint X η)
    (η : codimZeroPoints X) :
    ∃ c : OpenImmersionChart X, IsOpenImmersion c.ι ∧ Points.mapOfOver c.ι c.u = (η : Points X) :=
  sorry

/-- A chosen open-immersion chart through a codimension-zero point, obtained from the schematic
locus of `X`. -/
noncomputable def chosenOpenImmersionChart {S : Scheme.{u}} {X : AlgebraicSpace S}
    [HasFiniteIrreducibleComponentsOnCompactOpens X]
    (hweak : X.weakAss ⊆ codimZeroPoints X)
    (hmono : ∀ η ∈ codimZeroPoints X, existsMonoFieldValuedPoint X η)
    (η : codimZeroPoints X) : OpenImmersionChart X :=
  Classical.choose (exists_isOpenImmersion_chart_of_mem_codimZero hweak hmono η)

/-- The chosen chart through `η` is an open immersion sending its marked point to `η`. -/
theorem chosenOpenImmersionChart_spec {S : Scheme.{u}} {X : AlgebraicSpace S}
    [HasFiniteIrreducibleComponentsOnCompactOpens X]
    (hweak : X.weakAss ⊆ codimZeroPoints X)
    (hmono : ∀ η ∈ codimZeroPoints X, existsMonoFieldValuedPoint X η)
    (η : codimZeroPoints X) :
    IsOpenImmersion (chosenOpenImmersionChart hweak hmono η).ι ∧
      Points.mapOfOver (chosenOpenImmersionChart hweak hmono η).ι
        (chosenOpenImmersionChart hweak hmono η).u = (η : Points X) :=
  sorry

/-- The object `Spec(𝒪_{X,η})` of `Over S` associated to the chosen open-immersion chart
through a codimension-zero point. -/
noncomputable def codimZeroStalkOver {S : Scheme.{u}} {X : AlgebraicSpace S}
    [HasFiniteIrreducibleComponentsOnCompactOpens X]
    (hweak : X.weakAss ⊆ codimZeroPoints X)
    (hmono : ∀ η ∈ codimZeroPoints X, existsMonoFieldValuedPoint X η)
    (η : codimZeroPoints X) : Over S :=
  specStalkOver (chosenOpenImmersionChart hweak hmono η).U
    (chosenOpenImmersionChart hweak hmono η).u

/-- `codimZeroStalkOver` is `specStalkOver` of the chosen chart. -/
theorem codimZeroStalkOver_eq {S : Scheme.{u}} {X : AlgebraicSpace S}
    [HasFiniteIrreducibleComponentsOnCompactOpens X]
    (hweak : X.weakAss ⊆ codimZeroPoints X)
    (hmono : ∀ η ∈ codimZeroPoints X, existsMonoFieldValuedPoint X η)
    (η : codimZeroPoints X) :
    codimZeroStalkOver hweak hmono η =
      specStalkOver (chosenOpenImmersionChart hweak hmono η).U
        (chosenOpenImmersionChart hweak hmono η).u :=
  sorry

/-- The canonical morphism `j_η : Spec(𝒪_{X,η}) ⟶ X` of algebraic spaces, obtained as
`fromSpecStalk` of the chosen open-immersion chart through `η`. -/
noncomputable def codimZeroStalkMap {S : Scheme.{u}} {X : AlgebraicSpace S}
    [HasFiniteIrreducibleComponentsOnCompactOpens X]
    (hweak : X.weakAss ⊆ codimZeroPoints X)
    (hmono : ∀ η ∈ codimZeroPoints X, existsMonoFieldValuedPoint X η)
    (η : codimZeroPoints X) : ofOver (codimZeroStalkOver hweak hmono η) ⟶ X :=
  fromSpecStalk (chosenOpenImmersionChart hweak hmono η).ι
    (chosenOpenImmersionChart hweak hmono η).u

/-- `codimZeroStalkMap` is `fromSpecStalk` of the chosen open-immersion chart. -/
theorem codimZeroStalkMap_eq {S : Scheme.{u}} {X : AlgebraicSpace S}
    [HasFiniteIrreducibleComponentsOnCompactOpens X]
    (hweak : X.weakAss ⊆ codimZeroPoints X)
    (hmono : ∀ η ∈ codimZeroPoints X, existsMonoFieldValuedPoint X η)
    (η : codimZeroPoints X) :
    codimZeroStalkMap hweak hmono η =
      fromSpecStalk (chosenOpenImmersionChart hweak hmono η).ι
        (chosenOpenImmersionChart hweak hmono η).u :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
