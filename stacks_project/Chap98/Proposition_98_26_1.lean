/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FunctorOfPoints
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType.Point
public import ReasLib.RingTheory.Regular.GRing
public import stacks_project.Chap98.Lemma_98_25_4
public import stacks_project.Chap98.Lemma_98_27_16_Openness
public import stacks_project.Chap98.Proposition_98_26_1_Axioms
import Mathlib.Tactic.CrossRefAttribute

/-!
# Algebraic spaces in the Noetherian setting

A set-valued functor on locally Noetherian schemes over a locally Noetherian
base, with representable diagonal and Artin axioms [-1] through [5], extends
uniquely to an algebraic space on `(Sch/S)_fppf`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits Opposite
open AlgebraicGeometry.Scheme.Over
open AlgebraicGeometry.StandardTopology

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Universe lift of the functor of points of an algebraic space over `S`. -/
abbrev uliftFunctorOfPoints {S : Scheme.{u}} (X : AlgebraicSpace S) :
    (Over S)ᵒᵖ ⥤ Type (u + 1) :=
  X.functorOfPoints ⋙ uliftFunctor.{u + 1, u}

/-- `uliftFunctorOfPoints` is postcomposition of `functorOfPoints` with
`uliftFunctor`. -/
theorem uliftFunctorOfPoints_eq {S : Scheme.{u}} (X : AlgebraicSpace S) :
    uliftFunctorOfPoints X = X.functorOfPoints ⋙ uliftFunctor.{u + 1, u} :=
  sorry

/-- Proposition 98.26.1: let `S` be a locally Noetherian scheme and let
`F : (locallyNoetherian S).FullSubcategoryᵒᵖ ⥤ Type (u + 1)` be a functor on
`(Noetherian/S)_étale`. Assume the diagonal `diag F` is representable as a
transformation of functors in the sense of `uliftYoneda.relativelyRepresentable`,
`F` satisfies axioms [-1] (`boundedOnFiniteTypeFields`), [0]
(`Presheaf.IsSheaf` for `locallyNoetherianTopology StandardTopology.etale S`),
[1] (`Extension.PreservesDirectedAffineLimits`), [2] (`HasRimSchlessinger`),
[3] (`HasFiniteDimensionalTangentSpaces`), [4] (`HasEffectiveFormalObjects`),
and [5] (`OpennessOfVersality`), and `S.presheaf.stalk s` is a G-ring for every
finite type point `s` of `S`. Then there exists a unique algebraic space
`X : AlgebraicSpace S` on `(Sch/S)_fppf` whose restriction to
`(Noetherian/S)_étale` is `F`. -/
@[stacks 0GE7]
theorem existsUnique_of_noetherianArtinAxioms {S : Scheme.{u}}
    [AlgebraicGeometry.IsLocallyNoetherian S]
    {F : (locallyNoetherian S).FullSubcategoryᵒᵖ ⥤ Type (u + 1)}
    (hΔ : uliftYoneda.{u + 1}.relativelyRepresentable (Limits.diag F))
    (h_size : boundedOnFiniteTypeFields F)
    (h0 : Presheaf.IsSheaf (locallyNoetherianTopology StandardTopology.etale S) F)
    (h1 : Extension.PreservesDirectedAffineLimits (locallyNoetherian S) F)
    [HasRimSchlessinger F] [HasFiniteDimensionalTangentSpaces F]
    [HasEffectiveFormalObjects F] [OpennessOfVersality F]
    (hG : ∀ s : S, IsFiniteTypePoint s → IsGRing (S.presheaf.stalk s)) :
    ∃ X : AlgebraicSpace S,
      Nonempty ((restrictPresheaf S).obj (uliftFunctorOfPoints X) ≅ F) ∧
        ∀ Y : AlgebraicSpace S,
          Nonempty ((restrictPresheaf S).obj (uliftFunctorOfPoints Y) ≅ F) →
            Nonempty (uliftFunctorOfPoints X ≅ uliftFunctorOfPoints Y) :=
  sorry

/-- Existence in `existsUnique_of_noetherianArtinAxioms` is an algebraic space
whose restricted universe-lifted functor of points is naturally isomorphic to
`F`; uniqueness is uniqueness up to isomorphism of those universe-lifted
functors of points, not objectwise uniqueness of `AlgebraicSpace S`. -/
theorem existsUnique_of_noetherianArtinAxioms_spec {S : Scheme.{u}}
    [AlgebraicGeometry.IsLocallyNoetherian S]
    {F : (locallyNoetherian S).FullSubcategoryᵒᵖ ⥤ Type (u + 1)}
    (hΔ : uliftYoneda.{u + 1}.relativelyRepresentable (Limits.diag F))
    (h_size : boundedOnFiniteTypeFields F)
    (h0 : Presheaf.IsSheaf (locallyNoetherianTopology StandardTopology.etale S) F)
    (h1 : Extension.PreservesDirectedAffineLimits (locallyNoetherian S) F)
    [HasRimSchlessinger F] [HasFiniteDimensionalTangentSpaces F]
    [HasEffectiveFormalObjects F] [OpennessOfVersality F]
    (hG : ∀ s : S, IsFiniteTypePoint s → IsGRing (S.presheaf.stalk s)) :
    (∃ X : AlgebraicSpace S,
        Nonempty ((restrictPresheaf S).obj (uliftFunctorOfPoints X) ≅ F) ∧
          ∀ Y : AlgebraicSpace S,
            Nonempty ((restrictPresheaf S).obj (uliftFunctorOfPoints Y) ≅ F) →
              Nonempty (uliftFunctorOfPoints X ≅ uliftFunctorOfPoints Y)) ↔
      (∃ X : AlgebraicSpace S,
          Nonempty ((restrictPresheaf S).obj (uliftFunctorOfPoints X) ≅ F)) ∧
        ∀ X Y : AlgebraicSpace S,
          Nonempty ((restrictPresheaf S).obj (uliftFunctorOfPoints X) ≅ F) →
          Nonempty ((restrictPresheaf S).obj (uliftFunctorOfPoints Y) ≅ F) →
            Nonempty (uliftFunctorOfPoints X ≅ uliftFunctorOfPoints Y) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
