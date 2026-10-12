/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FormallySmooth
public import stacks_project.Chap66.Lemma_66_31_3_LocallyProjective
public import stacks_project.Chap76.Definition_76_7_2_Differentials
public import stacks_project.Chap76.Definition_76_21_1_NaiveCotangent
public import stacks_project.Chap76.Lemma_76_21_4_Homology

/-!
# Formal smoothness via the naive cotangent complex

A morphism of algebraic spaces is formally smooth if and only if the degree `-1`
homology of its naive cotangent complex vanishes and its sheaf of relative
differentials is locally projective.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules CategoryTheory.Limits
open scoped AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.FormallySmooth

/-- Lemma 76.21.6: Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of
algebraic spaces over `S`. Then `f` is formally smooth if and only if
`(NL[f]).homology (-1)` is zero and `Ω[f]` is locally projective. The source
identification of degree-zero homology with `Ω[f]` is
`Hom.NaiveCotangent.homologyZeroIso` from Lemma 76.21.4. -/
@[stacks 0D10]
theorem iff_naiveCotangent {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    FormallySmooth f ↔ IsZero ((NL[f]).homology (-1)) ∧ IsLocallyProjective Ω[f] :=
  sorry

/-- The degree `-1` homology of the naive cotangent complex of a formally smooth
morphism of algebraic spaces vanishes. -/
theorem isZero_homology_negOne {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    {f : X ⟶ Y} [FormallySmooth f] :
    IsZero ((NL[f]).homology (-1)) :=
  sorry

/-- A morphism of algebraic spaces whose naive cotangent complex has vanishing
degree `-1` homology and locally projective relative differentials is formally
smooth. -/
theorem of_naiveCotangent {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    (hH : IsZero ((NL[f]).homology (-1))) (hΩ : IsLocallyProjective Ω[f]) :
    FormallySmooth f :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.FormallySmooth
