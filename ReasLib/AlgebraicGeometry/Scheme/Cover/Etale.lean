/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Cover.QuasiCompact
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen

/-!
# Refinements of étale covers

Étale covers of affine schemes have finite refinements by affine open subschemes
of their members.
-/

@[expose] public section

open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Cover

/-- An étale cover of an affine scheme has a finite affine étale refinement whose
component maps into the original cover are open immersions. -/
theorem exists_finite_affineRefinement {T : Scheme.{u}} [IsAffine T]
    (𝒰 : T.Cover Scheme.etalePrecoverage) :
    ∃ (𝒱 : T.AffineCover (@Etale)) (f : 𝒱.cover ⟶ 𝒰),
      Finite 𝒱.I₀ ∧ ∀ j, IsOpenImmersion (f.h₀ j) := by
  -- Local instance justification (proof-local temporary data): affineness makes the
  -- target quasi-compact for the general quasi-compact-cover refinement theorem.
  let _ : CompactSpace T := by infer_instance
  -- Local instance justification (proof-local temporary data): the general refinement
  -- theorem requires the given étale cover packaged as a quasi-compact cover.
  let _ : QuasiCompactCover 𝒰.toPreZeroHypercover :=
    QuasiCompactCover.of_isOpenMap (K := Scheme.precoverage (@Etale)) fun i ↦ by
      -- Local instance justification (proof-local temporary data): expose the étale
      -- property stored by this cover while proving that its component is open.
      let _ : Etale (𝒰.f i) := Scheme.Cover.map_prop 𝒰 i
      exact Scheme.Hom.isOpenMap (𝒰.f i)
  simpa using (QuasiCompactCover.exists_hom 𝒰)

end AlgebraicGeometry.Scheme.Cover
