/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap66.Lemma_66_31_3_LocallyProjective
public import stacks_project.Chap76.Definition_76_7_2_Differentials
public import stacks_project.Chap76.Lemma_76_19_2_FormallySmooth

/-!
# Relative differentials of formally smooth morphisms of algebraic spaces

The sheaf of relative differentials of a formally smooth morphism of algebraic
spaces is locally projective.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules
open scoped AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.FormallySmooth

/-- Lemma 76.19.8: Let `S` be a scheme. Let `f : X ⟶ Y` be a formally smooth morphism of
algebraic spaces over `S`. Then `Ω[f]` is locally projective on `X`. -/
@[stacks 061I]
instance instIsLocallyProjectiveRelativeDifferentials {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [FormallySmooth f] :
    IsLocallyProjective Ω[f] :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.FormallySmooth
