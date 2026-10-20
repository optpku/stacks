module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
public import stacks_project.Chap67.Definition_67_40_1_Proper
public import stacks_project.Chap70.Lemma_70_19_1_IsoOverOpen
public import stacks_project.Chap80.Definition_80_3_1_RelativelyRepresentable
public import stacks_project.Chap98.Situation_98_27_1_Contraction

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Contraction.Triple

/-!
# Compatible contraction triples

In a contraction situation, a triple on a locally Noetherian scheme `V` over `S`
consists of a closed subset `Z ⊂ |V|`, a morphism `u'` from the open complement
of `Z` into `U'`, and an adic morphism `hatx` from the completion of `V` along
`Z` into `W`, together with the compatibility witness of a proper isomorphism
over `V \ Z`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace
open AlgebraicGeometry.AlgebraicSpace AlgebraicGeometry.Scheme.Over
open AlgebraicGeometry.AlgebraicSpace.SchemeRealization

universe u

#check (AlgebraicGeometry.AlgebraicSpace.ContractionSituation.CompatibilityWitness :
  ∀ {S : Scheme.{u}} [AlgebraicGeometry.IsLocallyNoetherian S]
    (σ : ContractionSituation S) (V : Over S) [AlgebraicGeometry.IsLocallyNoetherian V.left]
    (Z : Closeds (Points (ofOver V)))
    (u' : openComplementAlong (ofOver V) Z ⟶ σ.openComplement)
    (hatx : completionAlong (ofOver V) Z ⟶ σ.W), Type (u + 1))

#check (AlgebraicGeometry.AlgebraicSpace.ContractionSituation.Triple :
  ∀ {S : Scheme.{u}} [AlgebraicGeometry.IsLocallyNoetherian S]
    (σ : ContractionSituation S) (V : Over S) [AlgebraicGeometry.IsLocallyNoetherian V.left],
    Type (u + 1))
