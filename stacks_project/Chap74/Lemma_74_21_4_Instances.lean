/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.MorphismProperty.Local
public import stacks_project.Chap65.Lemma_65_12_4_Immersion
public import stacks_project.Chap74.Lemma_74_10_2_BaseChange
public import stacks_project.Chap74.Definition_74_21_1_EtaleSmoothLocal

/-!
# Étale-smooth locality from étale source and smooth target locality

A morphism property of algebraic spaces over a scheme `S` that is étale local
on the source, smooth local on the target, and stable under postcomposition
with open immersions is étale-smooth local on the source-and-target.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.IsEtaleSmoothLocalAtSourceAndTarget

/-- Étale locality on the source and smooth locality on the target, together with
stability under postcomposition with open immersions, implies étale-smooth
locality on source-and-target. -/
@[instance 100]
theorem of_isLocalAtSource_isLocalAtTarget {S : Scheme.{u}}
    (P : MorphismProperty (AlgebraicSpace S))
    [P.IsLocalAtSource etalePrecoverage]
    [P.IsLocalAtTarget (smoothPrecoverage S)]
    [P.RespectsRight (@IsOpenImmersion S : MorphismProperty (AlgebraicSpace S))] :
    IsEtaleSmoothLocalAtSourceAndTarget P :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.IsEtaleSmoothLocalAtSourceAndTarget
