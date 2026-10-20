/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalSpectrum.Comparison
import StacksCheckRecall

/-!
# Maps out of affine formal schemes, local stages

If some weak ideal of definition has local quotient, morphisms `Spec(A) ⟶ X`
over `S` are in bijection with morphisms `Spf(A) ⟶ X` over `S`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.AffineFormalAlgebraicSpace

noncomputable section

universe u

/- Lemma 87.33.2: Let `S` be a scheme. Let `A` be a weakly admissible
topological `S`-algebra such that `A ⧸ I` is a local ring for some weak
ideal of definition `I`. Let `X` be a scheme over `S`. Then the natural
map `Mor_S(Spec(A), X) ⟶ Mor_S(Spf(A), X)` is bijective. -/
@[stacks 0AQG] #check
  (AlgebraicGeometry.AffineFormalAlgebraicSpace.specHomToSpfHom_bijective_of_isLocalRing :
    ∀ {A : Type u} [CommRing A]
    [TopologicalSpace A] [TopologicalRing.IsWeaklyAdmissibleRing A]
    {S : Scheme.{u}} (structureHom : Spec (.of A) ⟶ S)
    [HasWeakSheafify (Scheme.fppfTopology.over S) (Type u)]
    (I : WeakIdealOfDefinition A) [IsLocalRing (A ⧸ I.ideal)] {X : Over S},
    Function.Bijective (specHomToSpfHom structureHom X))
