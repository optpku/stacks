/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Noetherian
public import ReasLib.RingTheory.AdicCompletion.AnalyticallyUnramified
public import stacks_project.Chap66.Definition_66_24_1_Noetherian
public import stacks_project.Chap67.Definition_67_39_1_Etale
public import stacks_project.Chap67.Lemma_67_23_5
public import stacks_project.Chap67.Lemma_67_24_2_FieldPoints
public import stacks_project.Chap67.Lemma_67_49_2
public import stacks_project.Chap67.Lemma_67_49_5_Normalization

/-!
# Finiteness of absolute normalization over an analytically unramified local ring
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The base scheme, viewed as an algebraic space over itself, is locally
Noetherian when the scheme is. -/
instance instIsLocallyNoetherian_ofOver_id {S : Scheme.{u}}
    [AlgebraicGeometry.IsLocallyNoetherian S] :
    IsLocallyNoetherian (ofOver (Over.mk (𝟙 S))) :=
  @instIsLocallyNoetherian_ofOver S (Over.mk (𝟙 S))
    (inferInstanceAs (AlgebraicGeometry.IsLocallyNoetherian S))

/-- An algebraic space locally of finite type over a locally Noetherian scheme is
locally Noetherian via its unique structure morphism. -/
instance instIsLocallyNoetherian_of_locallyOfFiniteType_toBase
    {S : Scheme.{u}} [AlgebraicGeometry.IsLocallyNoetherian S]
    (X : AlgebraicSpace S) [LocallyOfFiniteType (toBase X)] :
    IsLocallyNoetherian X :=
  LocallyOfFiniteType.isLocallyNoetherian (toBase X)

/-- Lemma 89.6.3: Let `(A, 𝔪)` be a local Noetherian ring. Let `X` be an algebraic
space over `A`. Assume `A` is analytically unramified, `X` is locally of finite
type over `A`, and `X ⟶ Spec(A)` is étale at every point of codimension `0` in
`X`. Then the normalization of `X` is finite over `X`. -/
@[stacks 0BHR]
theorem isFinite_normalizationTo_of_analyticallyUnramified_of_codimZeroEtale
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    [IsAnalyticallyUnramified A] (X : AlgebraicSpace (Spec (.of A)))
    [LocallyOfFiniteType (toBase X)]
    (h_etale : ∀ x : Points X, x ∈ codimZeroPoints X → EtaleAt (toBase X) x) :
    IsFinite X.normalizationTo :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
