/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Cover.Open
public import ReasLib.AlgebraicGeometry.Scheme.Sites.ChosenPresentation
public import ReasLib.CategoryTheory.Sites.Family.FormalCoproduct.Basis

/-!
# Realizing covers in chosen big-site presentations

Covers with represented sources can be represented up to componentwise
isomorphism. Arbitrary pro-étale covers instead admit bounded-site refinements
(see `BigProetaleSite.exists_coveringFamily_refining`).
-/

@[expose] public section

open CategoryTheory

universe u v

namespace AlgebraicGeometry.ChosenBigSite

variable {P : Precoverage Scheme.{u}}

/-- Zariski cover sources are open subschemes and satisfy the ordinary
big-site object bound (Stacks, Tag 000J and Sets, Lemma `what-is-in-it`). -/
instance : Scheme.HasBoundedCoverSources Scheme.zariskiPrecoverage where
  source_size_le_bound := by sorry

/-- An ambient cover whose sources are represented is tautologically equivalent
to the image of a covering family in the chosen carrier. The source hypothesis
is local to this cover, rather than a closure condition on all ambient covers. -/
theorem exists_coveringFamily_tautologicallyEquivalent_of_sources
    (X : ChosenBigSite.{u, v} P) {T : X.carrier}
    (𝒰 : Scheme.Cover.{u} P (X.toScheme.obj T))
    (hsources : ∀ i : 𝒰.I₀, ∃ Y : X.carrier, Nonempty (X.toScheme.obj Y ≅ 𝒰.X i)) :
    ∃ 𝒱 : Limits.FormalCoproduct.{u} (CategoryTheory.Over T),
      Limits.FormalCoproduct.IsCovering
          (@Pretopology.toPrecoverage X.carrier (Cat.str X.carrier)
            X.hasPullbacks X.pretopology) 𝒱 ∧
        Limits.FormalCoproduct.TautologicallyEquivalent
          ((Limits.FormalCoproduct.map
            (CategoryTheory.Over.post (X := T) X.toScheme)).obj 𝒱)
          (Limits.FormalCoproduct.ofArrows 𝒰.X 𝒰.f) := sorry

/-- Covers for a precoverage with bounded sources (in particular Zariski covers)
can be represented tautologically in a chosen big site. No instance of the
bounded-source condition is asserted for the pro-étale precoverage. -/
theorem exists_coveringFamily_tautologicallyEquivalent
    [Scheme.HasBoundedCoverSources P]
    (X : ChosenBigSite.{u, v} P) {T : X.carrier}
    (𝒰 : Scheme.Cover.{u} P (X.toScheme.obj T)) :
    ∃ 𝒱 : Limits.FormalCoproduct.{u} (CategoryTheory.Over T),
      Limits.FormalCoproduct.IsCovering
          (@Pretopology.toPrecoverage X.carrier (Cat.str X.carrier)
            X.hasPullbacks X.pretopology) 𝒱 ∧
        Limits.FormalCoproduct.TautologicallyEquivalent
          ((Limits.FormalCoproduct.map
            (CategoryTheory.Over.post (X := T) X.toScheme)).obj 𝒱)
          (Limits.FormalCoproduct.ofArrows 𝒰.X 𝒰.f) :=
  exists_coveringFamily_tautologicallyEquivalent_of_sources X 𝒰
    (fun i => X.spec.coverSource_exists_iso 𝒰 i
      (Scheme.HasBoundedCoverSources.source_size_le_bound 𝒰 i))

/-- Every ambient cover admits a covering refinement in the chosen presentation.
This is the Stacks 098J interface and carries no hypothesis that its sources
are individually represented. -/
theorem exists_coveringFamily_refining
    (X : ChosenBigSite.{u, v} P) {T : X.carrier}
    (𝒰 : Scheme.Cover.{u} P (X.toScheme.obj T)) :
    ∃ 𝒱 : Limits.FormalCoproduct.{u} (CategoryTheory.Over T),
      Limits.FormalCoproduct.IsCovering
          (@Pretopology.toPrecoverage X.carrier (Cat.str X.carrier)
            X.hasPullbacks X.pretopology) 𝒱 ∧
        Nonempty
          (((Limits.FormalCoproduct.map
            (CategoryTheory.Over.post (X := T) X.toScheme)).obj 𝒱) ⟶
            Limits.FormalCoproduct.ofArrows 𝒰.X 𝒰.f) :=
  X.spec.covering_exists_refinement 𝒰

end AlgebraicGeometry.ChosenBigSite
