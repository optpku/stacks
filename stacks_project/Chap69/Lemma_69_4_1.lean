/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects
public import stacks_project.Chap66.Lemma_66_18_12_Pushforward
public import stacks_project.Chap67.Definition_67_45_2_Integral

/-!
# Exactness of small étale abelian pushforward along integral morphisms

For an integral morphism of algebraic spaces, the small étale abelian
direct image is exact, and the higher direct images vanish in positive degree.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

-- Local instance justification (defeq pin): `HasInjectiveResolutions` and `Functor.rightDerived` pin the Abelian-induced `Preadditive`/`HasZeroMorphisms` instances for defeq of `higherDirectImage`.
attribute [local instance 2000] Abelian.toPreadditive Preadditive.preadditiveHasZeroMorphisms

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [IsIntegralHom f]

/-- Lemma 69.4.1 (1): let `S` be a scheme. Let `f : X ⟶ Y` be an integral morphism of
algebraic spaces over `S` (for example a finite morphism). Then
`sheafPushforwardAbelian f : Sheaf (smallEtaleTopology X) AddCommGrpCat ⥤
Sheaf (smallEtaleTopology Y) AddCommGrpCat` is an exact functor. -/
@[stacks 0A4K]
theorem sheafPushforwardAbelian_exact_of_isIntegralHom :
    exactFunctor _ _ (sheafPushforwardAbelian f) :=
  sorry

/-- The small étale abelian direct image along an integral morphism of algebraic spaces
preserves finite colimits. -/
instance sheafPushforwardAbelian_preservesFiniteColimits_of_isIntegralHom :
    PreservesFiniteColimits (sheafPushforwardAbelian f) :=
  sorry

/-- Lemma 69.4.1 (2): let `S` be a scheme. Let `f : X ⟶ Y` be an integral morphism of
algebraic spaces over `S` (for example a finite morphism), and let `F` be an abelian
sheaf on the small étale site of `X`. Then `higherDirectImage f F p` is zero for
`0 < p`. -/
@[stacks 0A4K]
theorem higherDirectImage_isZero_of_isIntegralHom
    [HasSheafify (smallEtaleTopology X) AddCommGrpCat.{u + 1}]
    [HasSheafify (smallEtaleTopology Y) AddCommGrpCat.{u + 1}]
    [Abelian (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})]
    [Abelian (Sheaf (smallEtaleTopology Y) AddCommGrpCat.{u + 1})]
    [HasInjectiveResolutions (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})]
    [(sheafPushforward AddCommGrpCat.{u + 1} f).Additive]
    (F : Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1}) (p : ℕ) (hp : 0 < p) :
    IsZero (higherDirectImage f F p) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
