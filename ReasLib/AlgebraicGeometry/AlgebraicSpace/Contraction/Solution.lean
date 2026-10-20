/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Contraction
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CompletionAlong.Transport
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Proper
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.IsoOverOpen

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace TypeCat
open AlgebraicGeometry.AlgebraicSpace.SchemeRealization

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace ContractionSituation

variable {S : Scheme.{u}} [AlgebraicGeometry.IsLocallyNoetherian S]

/-- A solution of a contraction situation relative to an arbitrary algebraic space
`X` over `S`: a proper morphism `f : X' ⟶ X`, a closed
subset `T ⊂ |X|`, and an isomorphism `a : X_/T ⟶ W` such that `T'` is the
inverse image of `T`, `f` is an isomorphism over `X \ T`, and
`g = a ∘ f_/T`. -/
structure SolutionFor (σ : ContractionSituation S) (X : AlgebraicSpace S) where
  /-- The morphism `f : X' ⟶ X`. -/
  f : σ.X' ⟶ X
  /-- `f` is proper. -/
  proper_f : Proper f
  /-- The closed subset `T ⊂ |X|`. -/
  T : Closeds (Points X)
  /-- The morphism `a : X_/T ⟶ W` of formal algebraic spaces. -/
  a : completionAlong X T ⟶ σ.W
  /-- `a` is an isomorphism. -/
  isIso_a : IsIso a
  /-- `T'` is the inverse image of `T` under `|f|`. -/
  inverseImage : σ.T' = T.preimage (Points.continuous_map f)
  /-- `f` identifies `U'` with the open complement `X \ T`. -/
  isoOverOpen : IsIsoOverOpen f (AlgebraicSpace.openComplementι X T)
  /-- `g = a ∘ f_/T` after transporting the completion of `X'` along
  `inverseImage`. -/
  commutes :
    completionAlong.congrClosed inverseImage ≫ completionAlong.map f T ≫ a = σ.g

namespace SolutionFor

variable {σ : ContractionSituation S} {X : AlgebraicSpace S}

/-- Package a morphism `f : X' ⟶ X`, a closed subset `T ⊂ |X|`, and a morphism
`a : X_/T ⟶ W` as a solution. -/
def of (f : σ.X' ⟶ X) (T : Closeds (Points X))
    (a : completionAlong X T ⟶ σ.W)
    (proper_f : Proper f) (isIso_a : IsIso a)
    (inverseImage : σ.T' = T.preimage (Points.continuous_map f))
    (isoOverOpen : IsIsoOverOpen f (AlgebraicSpace.openComplementι X T))
    (commutes : completionAlong.congrClosed inverseImage ≫ completionAlong.map f T ≫ a = σ.g) :
    SolutionFor σ X where
  f := f
  T := T
  a := a
  proper_f := proper_f
  isIso_a := isIso_a
  inverseImage := inverseImage
  isoOverOpen := isoOverOpen
  commutes := commutes

/-- A solution records a proper morphism, an isomorphism of completions, the
inverse-image relation, an isomorphism over the open complement, and
commutativity with `g`. -/
theorem spec (sol : SolutionFor σ X) :
    Proper sol.f ∧ IsIso sol.a ∧
      σ.T' = sol.T.preimage (Points.continuous_map sol.f) ∧
      IsIsoOverOpen sol.f (AlgebraicSpace.openComplementι X sol.T) ∧
      completionAlong.congrClosed sol.inverseImage ≫
          completionAlong.map sol.f sol.T ≫ sol.a =
        σ.g :=
  ⟨sol.proper_f, sol.isIso_a, sol.inverseImage, sol.isoOverOpen, sol.commutes⟩

/-- The induced morphism `f_/T : X'_/T' ⟶ X_/T` of completions. -/
def mapCompletion (sol : SolutionFor σ X) :
    σ.completion ⟶ completionAlong X sol.T :=
  completionAlong.congrClosed sol.inverseImage ≫
    completionAlong.map sol.f sol.T

/-- Postcomposing `mapCompletion` with `a` recovers `g`. -/
theorem mapCompletion_comp (sol : SolutionFor σ X) :
    sol.mapCompletion ≫ sol.a = σ.g :=
  sol.commutes

end SolutionFor

end ContractionSituation

end AlgebraicGeometry.AlgebraicSpace
