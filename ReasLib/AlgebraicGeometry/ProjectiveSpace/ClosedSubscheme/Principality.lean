/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.ProjectiveSpace.ClosedSubscheme
public import ReasLib.AlgebraicGeometry.Scheme.EmbeddedPoints
public import Mathlib.RingTheory.Ideal.IsPrincipal
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Principal homogeneous ideals of projective closed subschemes

Codimension-one closed subschemes without embedded points over a Noetherian unique
factorization domain have principal homogeneous ideals.
-/

@[expose] public section

open Set TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.ProjectiveSpace.ClosedSubscheme

/-- Over a Noetherian unique factorization domain, the homogeneous twist ideal of a closed
subscheme of standard projective space is principal when the subscheme has no embedded points
and every irreducible component has ambient codimension one. -/
@[stacks 0BXL]
theorem twistIdeal_isPrincipal_of_noEmbeddedPoints_of_codimensionOne
    (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [UniqueFactorizationMonoid R] (n : ℕ)
    (Z : (ProjectiveSpace.scheme R n).IdealSheafData)
    (P : ProjTwistPresentation (ProjectiveSpace.grading R n))
    (h_noEmbeddedPoints : Z.subscheme.embeddedPoints = (∅ : Set Z.subscheme))
    (h_codimensionOne :
      ∀ ξ : Z.subscheme, ξ ∈ genericPoints Z.subscheme →
        ringKrullDim ((ProjectiveSpace.scheme R n).presheaf.stalk
          (Z.subschemeι.base ξ)) = 1) :
    (twistIdeal n Z P).toIdeal.IsPrincipal := sorry

/-- A closed subscheme of projective `n`-space has components of dimension `n - 1` if this
holds for every irreducible component when `n` is positive; when `n = 0`, it has no irreducible
components. -/
def ComponentsHaveDimension (k : Type u) [Field k] (n : ℕ)
    (Z : (ProjectiveSpace.scheme k n).IdealSheafData) : Prop :=
  if 0 < n then
    ∀ C : irreducibleComponents Z.subscheme,
      topologicalKrullDim (C : Set Z.subscheme) = ((n - 1 : ℕ) : WithBot ℕ∞)
  else
    IsEmpty (irreducibleComponents Z.subscheme)

/-- If every irreducible component of a projective closed subscheme has dimension `n - 1`,
then the ambient local ring at each generic point has Krull dimension one. -/
theorem codimensionOne_of_componentsHaveDimension
    (k : Type u) [Field k] (n : ℕ)
    (Z : (ProjectiveSpace.scheme k n).IdealSheafData)
    (h_componentDim : ComponentsHaveDimension k n Z) :
    ∀ ξ : Z.subscheme, ξ ∈ genericPoints Z.subscheme →
      ringKrullDim ((ProjectiveSpace.scheme k n).presheaf.stalk
        (Z.subschemeι.base ξ)) = 1 := sorry

/-- The homogeneous twist ideal of a projective closed subscheme over a field is principal
when the subscheme has no embedded points and all its irreducible components have dimension
one less than the ambient projective space. -/
@[stacks 0BXU]
theorem twistIdeal_isPrincipal_of_noEmbeddedPoints_of_componentsHaveDimension
    (k : Type u) [Field k] (n : ℕ)
    (Z : (ProjectiveSpace.scheme k n).IdealSheafData)
    (P : ProjTwistPresentation (ProjectiveSpace.grading k n))
    (h_noEmbeddedPoints : Z.subscheme.embeddedPoints = (∅ : Set Z.subscheme))
    (h_componentDim : ComponentsHaveDimension k n Z) :
    (twistIdeal n Z P).toIdeal.IsPrincipal := sorry

/-- The homogeneous twist ideal of a closed subscheme of the projective plane is principal
when every irreducible component has dimension one and the subscheme has no embedded points. -/
theorem planeCurveTwistIdeal_isPrincipal
    (k : Type u) [Field k]
    (Z : (ProjectiveSpace.scheme k 2).IdealSheafData)
    (P : ProjTwistPresentation (ProjectiveSpace.grading k 2))
    (h_noEmbeddedPoints : Z.subscheme.embeddedPoints = (∅ : Set Z.subscheme))
    (h_componentDim : ∀ C : irreducibleComponents Z.subscheme,
      topologicalKrullDim (C : Set Z.subscheme) = 1) :
    (twistIdeal 2 Z P).toIdeal.IsPrincipal := sorry

end AlgebraicGeometry.ProjectiveSpace.ClosedSubscheme
