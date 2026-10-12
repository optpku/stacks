/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Properties
public import ReasLib.Topology.ConstructibleTopology.Maps
public import ReasLib.Topology.ConstructibleTopology.Specialization
import Mathlib.Tactic.CrossRefAttribute

/-!
# Specializing points under quasi-compact dominant morphisms

A quasi-compact dominant morphism of schemes meets the generalization cone of every target
point. The proof reduces over an affine target neighbourhood to a map between spectral spaces,
where the image is closed in the constructible topology.
-/

@[expose] public section

noncomputable section

open CategoryTheory Topology
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- A point of the target of a quasi-compact dominant scheme morphism is a specialization of the
image of some source point. -/
@[stacks 02JQ "specializing preimages of quasi-compact dominant morphisms"]
theorem exists_specializing_preimage {X Y : Scheme.{u}} (f : X ⟶ Y)
    [QuasiCompact f] [IsDominant f] (y : Y) :
    ∃ x : X, f x ⤳ y := by
  obtain ⟨U, hU, hyU, -⟩ :=
    exists_isAffineOpen_mem_and_subset (X := Y) (U := ⊤) (x := y) (by simp)
  -- Local instance justification (proof-local temporary data): the chosen affine neighborhood needs its affine structure only while forming the restricted morphism.
  letI : IsAffine (U : Scheme.{u}) := hU
  -- Local instance justification (proof-local temporary data): the restricted dominant morphism needs its induced dominance instance only inside this affine-neighborhood argument.
  haveI : IsDominant (f ∣_ U) :=
    IsZariskiLocalAtTarget.restrict (show IsDominant f from inferInstance) U
  -- Local instance justification (proof-local temporary data): the compact preimage needs its compactness instance only to choose an affine spectral presentation.
  haveI : CompactSpace (f ⁻¹ᵁ U) :=
    QuasiCompact.compactSpace_of_compactSpace (f ∣_ U)
  obtain ⟨R, p, hp⟩ := compactSpace_iff_exists.mp
    (show CompactSpace (f ⁻¹ᵁ U) from inferInstance)
  let q : Spec R ⟶ (U : Scheme.{u}) := p ≫ (f ∣_ U)
  -- Local instance justification (proof-local temporary data): the auxiliary quasi-compact morphism q needs this inferred instance only for the spectral-map argument.
  haveI : QuasiCompact q :=
    HasAffineProperty.iff_of_isAffine.mpr (by infer_instance)
  -- Local instance justification (proof-local temporary data): the auxiliary dominant morphism q needs this derived instance only for the constructible-closure argument.
  haveI : IsDominant q := by
    rw [show q = p ≫ (f ∣_ U) from rfl]
    exact ⟨(f ∣_ U).denseRange.comp hp.denseRange (f ∣_ U).continuous⟩
  -- Local instance justification (proof-local temporary data): the affine-spectrum spectral structure is used only to apply the constructible-topology map results to q.
  letI : SpectralSpace (Spec R) := { }
  -- Local instance justification (proof-local temporary data): the affine-open spectral structure is used only to apply the constructible-topology map results to q.
  letI : SpectralSpace (U : Scheme.{u}) := { }
  have hclosed : IsClosed[constructibleTopology (U : Scheme.{u})] (Set.range q) :=
    q.isSpectralMap.isClosed_range_constructibleTopology
  obtain ⟨r, ⟨r', hr'⟩, hry⟩ :=
    hclosed.exists_specializingPoint_of_mem_closure
      (q.denseRange (⟨y, hyU⟩ : U))
  subst r
  refine ⟨(f ⁻¹ᵁ U).ι (p r'), ?_⟩
  simpa [q] using hry.map U.ι.continuous

end AlgebraicGeometry.Scheme.Hom
