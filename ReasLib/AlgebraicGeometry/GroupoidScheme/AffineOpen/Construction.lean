/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidScheme.AffineOpen.NormCut
public import ReasLib.AlgebraicGeometry.Scheme.Module.Picard.Norm.Construction
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteLocallyFree.Operations

/-!
# Affine presentations of determinantal norm cuts

The saturation complement `W'` and finite prime avoidance give a principal orbit
neighbourhood `D(f) ≤ W'`. On the already affine `D(f)`, a local projective-section norm
or a supplied sheaf norm gives another principal open. Two native principal-open
affineness proofs give a Spec presentation independently of its norm-cut identification.
The finite locally free producer uses the descended local determinant norm, with no
supplied norm or section-algebra projectivity assumption.
-/

@[expose] public section

open CategoryTheory TopologicalSpace Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidScheme.AffineOpenConstruction

variable {S : Scheme.{u}} (G : GroupoidScheme S) [IsFinite G.t.left]
  (N : Scheme.FiniteMorphismNorm G.s.left)

section ProjectiveSections

variable (W : G.U.left.affineOpens) (f : Γ(G.U.left, W))
  [Module.Finite (Γ(G.U.left, G.U.left.basicOpen f))
    (Γ(G.R.left, G.s.left ⁻¹ᵁ G.U.left.basicOpen f))]
  [Module.Projective (Γ(G.U.left, G.U.left.basicOpen f))
    (Γ(G.R.left, G.s.left ⁻¹ᵁ G.U.left.basicOpen f))]

/-- Compute the norm directly in the finite-projective section algebra over `D(f)`.
No global sheaf norm is an input to this local construction. -/
def projectiveNormSectionOnBasicOpen
    (hf : G.U.left.basicOpen f ≤ invariantInterior G W) :
    Γ(G.U.left, G.U.left.basicOpen f) :=
  Scheme.finiteProjectiveSectionNorm G.s.left (G.U.left.basicOpen f)
    (G.t.left.appLE W (G.s.left ⁻¹ᵁ G.U.left.basicOpen f)
      ((G.s.left.preimage_mono hf).trans (preimage_invariantInterior_le G W)) f)

/-- The determinantal basic open, constructed from the section algebra itself. -/
def projectiveAffineNormCut
    (hf : G.U.left.basicOpen f ≤ invariantInterior G W) : G.U.left.affineOpens :=
  ⟨G.U.left.basicOpen (projectiveNormSectionOnBasicOpen G W f hf),
    (W.2.basicOpen f).basicOpen _⟩

/-- The local determinantal basic open has a native Spec presentation. -/
def projectiveAffineNormCutPresentation
    (hf : G.U.left.basicOpen f ≤ invariantInterior G W) :
    Spec Γ(G.U.left, projectiveAffineNormCut G W f hf) ≅
      (projectiveAffineNormCut G W f hf : Scheme) :=
  (projectiveAffineNormCut G W f hf).2.isoSpec.symm

/-- The determinantal cut lies in the original principal open. -/
theorem projectiveAffineNormCut_le
    (hf : G.U.left.basicOpen f ≤ invariantInterior G W) :
    (projectiveAffineNormCut G W f hf : G.U.left.Opens) ≤ G.U.left.basicOpen f :=
  G.U.left.basicOpen_le _

/-- For an affine source morphism, the determinant is nonzero precisely when the target
pullback of `f` is nonzero everywhere in the source fibre. -/
theorem mem_projectiveAffineNormCut_iff [IsAffineHom G.s.left]
    (hf : G.U.left.basicOpen f ≤ invariantInterior G W) (x : G.U.left) :
    x ∈ (projectiveAffineNormCut G W f hf : G.U.left.Opens) ↔
      x ∈ G.U.left.basicOpen f ∧
        ∀ r : G.R.left, G.s.left r = x → G.t.left r ∈ G.U.left.basicOpen f := sorry

end ProjectiveSections

/-- Restrict the norm of the target pullback to the already affine principal open `D(f)`. -/
def normSectionOnBasicOpen (W : G.U.left.affineOpens) (f : Γ(G.U.left, W))
    (hf : G.U.left.basicOpen f ≤ invariantInterior G W) :
    Γ(G.U.left, G.U.left.basicOpen f) :=
  G.U.left.presheaf.map (homOfLE hf).op (normSectionOfNorm G N W f)

/-- An actual affine open: the basic open of the restricted norm on the affine `D(f)`. -/
def affineNormCutOfSection (W : G.U.left.affineOpens) (f : Γ(G.U.left, W))
    (hf : G.U.left.basicOpen f ≤ invariantInterior G W) : G.U.left.affineOpens :=
  ⟨G.U.left.basicOpen (normSectionOnBasicOpen G N W f hf),
    (W.2.basicOpen f).basicOpen _⟩

/-- Without a condition on the supplied norm, this is exactly the intersection of `D(f)`
with its nonvanishing locus on `W'`. -/
theorem affineNormCutOfSection_eq_inf (W : G.U.left.affineOpens)
    (f : Γ(G.U.left, W)) (hf : G.U.left.basicOpen f ≤ invariantInterior G W) :
    (affineNormCutOfSection G N W f hf : G.U.left.Opens) =
      G.U.left.basicOpen f ⊓ normCutOfNorm G N W f :=
  G.U.left.basicOpen_res _ _

/-- The constructed affine cut is contained in `D(f)`. -/
theorem affineNormCutOfSection_le_basicOpen (W : G.U.left.affineOpens)
    (f : Γ(G.U.left, W)) (hf : G.U.left.basicOpen f ≤ invariantInterior G W) :
    (affineNormCutOfSection G N W f hf : G.U.left.Opens) ≤ G.U.left.basicOpen f :=
  G.U.left.basicOpen_le _

/-- The constructed affine cut lies in the invariant interior. -/
theorem affineNormCutOfSection_le_invariantInterior (W : G.U.left.affineOpens)
    (f : Γ(G.U.left, W)) (hf : G.U.left.basicOpen f ≤ invariantInterior G W) :
    (affineNormCutOfSection G N W f hf : G.U.left.Opens) ≤ invariantInterior G W :=
  (affineNormCutOfSection_le_basicOpen G N W f hf).trans hf

/-- The Spec presentation uses the proved affineness of two successive basic opens of `W`.
It does not use affineness or invertibility obtained from an admitted theorem. -/
def affineNormCutOfSectionPresentation (W : G.U.left.affineOpens)
    (f : Γ(G.U.left, W)) (hf : G.U.left.basicOpen f ≤ invariantInterior G W) :
    Spec Γ(G.U.left, affineNormCutOfSection G N W f hf) ≅
      (affineNormCutOfSection G N W f hf : Scheme) :=
  (affineNormCutOfSection G N W f hf).2.isoSpec.symm

/-- The actual affine chart morphism into the object scheme. -/
def affineNormCutOfSectionChart (W : G.U.left.affineOpens)
    (f : Γ(G.U.left, W)) (hf : G.U.left.basicOpen f ≤ invariantInterior G W) :
    Spec Γ(G.U.left, affineNormCutOfSection G N W f hf) ⟶ G.U.left :=
  (affineNormCutOfSection G N W f hf).2.fromSpec

/-- The chart is the presentation followed by the open-subscheme inclusion. -/
theorem affineNormCutOfSectionChart_eq (W : G.U.left.affineOpens)
    (f : Γ(G.U.left, W)) (hf : G.U.left.basicOpen f ≤ invariantInterior G W) :
    affineNormCutOfSectionChart G N W f hf =
      (affineNormCutOfSectionPresentation G N W f hf).hom ≫
        (affineNormCutOfSection G N W f hf : G.U.left.Opens).ι := rfl

/-- The range of the constructed chart is precisely the constructed affine open. -/
theorem range_affineNormCutOfSectionChart (W : G.U.left.affineOpens)
    (f : Γ(G.U.left, W)) (hf : G.U.left.basicOpen f ≤ invariantInterior G W) :
    Set.range (affineNormCutOfSectionChart G N W f hf) =
      (affineNormCutOfSection G N W f hf : Set G.U.left) :=
  (affineNormCutOfSection G N W f hf).2.range_fromSpec

/-- A determinantal norm is nonzero exactly when the section is nonzero at every point of
the source fibre. Only finite local freeness of the source is needed for this norm formula. -/
theorem mem_normCutOfNorm_iff [IsFiniteLocallyFree G.s.left] (hN : N.IsDeterminant)
    (W : G.U.left.Opens) (f : Γ(G.U.left, W)) (x : G.U.left) :
    x ∈ normCutOfNorm G N W f ↔
      x ∈ invariantInterior G W ∧
        ∀ r : G.R.left, G.s.left r = x → G.t.left r ∈ G.U.left.basicOpen f := sorry

/-- The identity arrow implies that the determinantal norm cut on `W'` lies in `D(f)`. -/
theorem normCutOfNorm_le_basicOpen [IsFiniteLocallyFree G.s.left] (hN : N.IsDeterminant)
    (W : G.U.left.Opens) (f : Γ(G.U.left, W)) :
    normCutOfNorm G N W f ≤ G.U.left.basicOpen f := by
  intro x hx
  have hs : G.s.left (G.e.left x) = x := by
    simpa using congrArg (fun f ↦ f.left x) G.identity_source
  have ht : G.t.left (G.e.left x) = x := by
    simpa using congrArg (fun f ↦ f.left x) G.identity_target
  simpa [ht] using ((mem_normCutOfNorm_iff G N hN W f x).mp hx).2 (G.e.left x) hs

/-- Identify the already constructed affine open with the nonvanishing locus on `W'`.
This equality is not used to construct the presentation. -/
theorem affineNormCutOfSection_eq_normCut [IsFiniteLocallyFree G.s.left]
    (hN : N.IsDeterminant) (W : G.U.left.affineOpens) (f : Γ(G.U.left, W))
    (hf : G.U.left.basicOpen f ≤ invariantInterior G W) :
    (affineNormCutOfSection G N W f hf : G.U.left.Opens) = normCutOfNorm G N W f := by
  rw [affineNormCutOfSection_eq_inf]
  exact inf_eq_right.mpr (normCutOfNorm_le_basicOpen G N hN W f)

/-- Groupoid composition preserves the condition that `f` is nonzero along the entire orbit. -/
theorem normCutOfNorm_isOpenInvariant [IsFiniteLocallyFree G.s.left]
    (hN : N.IsDeterminant) (W : G.U.left.Opens) (f : Γ(G.U.left, W)) :
    G.toPreRelation.IsOpenInvariant (normCutOfNorm G N W f) := by
  have hsP : G.toPreRelation.s = G.s := by
    change Limits.prod.lift G.t G.s ≫ Limits.prod.snd = G.s
    exact Limits.prod.lift_snd G.t G.s
  have htP : G.toPreRelation.t = G.t := by
    change Limits.prod.lift G.t G.s ≫ Limits.prod.fst = G.t
    exact Limits.prod.lift_fst G.t G.s
  change Set.MapsTo _ _ _
  rw [hsP, htP]
  intro r hr
  have hPullback :
      IsPullback (Limits.pullback.fst G.s G.t).left
        (Limits.pullback.snd G.s G.t).left G.s.left G.t.left := by
    simpa using (IsPullback.of_hasPullback G.s G.t).map (Over.forget S)
  obtain ⟨hrW, hrnonzero⟩ := (mem_normCutOfNorm_iff G N hN W f (G.s.left r)).mp hr
  apply (mem_normCutOfNorm_iff G N hN W f (G.t.left r)).mpr
  constructor
  · apply (mem_invariantInterior G W _).mpr
    rintro ⟨q, hqW, hqt⟩
    have hi_source : G.s.left (G.i.left r) = G.t.left r := by
      simpa using congrArg (fun f ↦ f.left r) G.inverse_source
    have hi_target : G.t.left (G.i.left r) = G.s.left r := by
      simpa using congrArg (fun f ↦ f.left r) G.inverse_target
    obtain ⟨p, hp_fst, hp_snd⟩ := Scheme.exists_preimage_of_isPullback hPullback
      (G.i.left r) q (hi_source.trans hqt.symm)
    have hs : G.s.left (G.c.left p) = G.s.left q := by
      simpa [hp_snd] using congrArg (fun f ↦ f.left p) G.comp_source
    have ht : G.t.left (G.c.left p) = G.s.left r := by
      simpa [hp_fst, hi_target] using congrArg (fun f ↦ f.left p) G.comp_target
    exact hrW ⟨G.c.left p, by simpa [Set.mem_preimage, hs] using hqW, ht⟩
  · intro q hqs
    obtain ⟨p, hp_fst, hp_snd⟩ := Scheme.exists_preimage_of_isPullback hPullback q r hqs
    have hs : G.s.left (G.c.left p) = G.s.left r := by
      simpa [hp_snd] using congrArg (fun f ↦ f.left p) G.comp_source
    have ht : G.t.left (G.c.left p) = G.t.left q := by
      simpa [hp_fst] using congrArg (fun f ↦ f.left p) G.comp_target
    simpa [ht] using hrnonzero (G.c.left p) hs

/-- The source's norm cut, with the principal section chosen by proved finite prime avoidance. -/
def orbitAffineNormCut [IsFinite G.s.left] (u : G.U.left) (W : G.U.left.affineOpens)
    (hW : G.t.left '' (G.s.left ⁻¹' {u}) ⊆ W) : G.U.left.affineOpens :=
  affineNormCutOfSection G N W (orbitSection G u W hW) (orbitSection_spec G u W hW).2

/-- The actual Spec presentation of the orbit norm cut. -/
def orbitAffineNormCutPresentation [IsFinite G.s.left] (u : G.U.left)
    (W : G.U.left.affineOpens) (hW : G.t.left '' (G.s.left ⁻¹' {u}) ⊆ W) :
    Spec Γ(G.U.left, orbitAffineNormCut G N u W hW) ≅
      (orbitAffineNormCut G N u W hW : Scheme) :=
  affineNormCutOfSectionPresentation G N W (orbitSection G u W hW)
    (orbitSection_spec G u W hW).2

/-- The orbit cut lies in the caller's affine neighbourhood. -/
theorem orbitAffineNormCut_le [IsFinite G.s.left] (u : G.U.left)
    (W : G.U.left.affineOpens) (hW : G.t.left '' (G.s.left ⁻¹' {u}) ⊆ W) :
    (orbitAffineNormCut G N u W hW : G.U.left.Opens) ≤ W :=
  (affineNormCutOfSection_le_basicOpen G N W (orbitSection G u W hW)
    (orbitSection_spec G u W hW).2).trans (G.U.left.basicOpen_le _)

/-- The chosen base point belongs to the determinantal orbit norm cut. -/
theorem mem_orbitAffineNormCut [IsFinite G.s.left] [IsFiniteLocallyFree G.s.left]
    (hN : N.IsDeterminant) (u : G.U.left) (W : G.U.left.affineOpens)
    (hW : G.t.left '' (G.s.left ⁻¹' {u}) ⊆ W) :
    u ∈ (orbitAffineNormCut G N u W hW : G.U.left.Opens) := by
  rw [orbitAffineNormCut, affineNormCutOfSection_eq_normCut G N hN,
    mem_normCutOfNorm_iff G N hN]
  have hs : G.s.left (G.e.left u) = u := by
    simpa using congrArg (fun f ↦ f.left u) G.identity_source
  have ht : G.t.left (G.e.left u) = u := by
    simpa using congrArg (fun f ↦ f.left u) G.identity_target
  refine ⟨orbit_subset_invariantInterior G u W hW ⟨G.e.left u, hs, ht⟩, ?_⟩
  intro r hr
  exact (orbitSection_spec G u W hW).1 ⟨r, hr, rfl⟩

/-- The determinantal orbit norm cut is invariant under the groupoid relation. -/
theorem orbitAffineNormCut_isOpenInvariant [IsFinite G.s.left]
    [IsFiniteLocallyFree G.s.left] (hN : N.IsDeterminant) (u : G.U.left)
    (W : G.U.left.affineOpens) (hW : G.t.left '' (G.s.left ⁻¹' {u}) ⊆ W) :
    G.toPreRelation.IsOpenInvariant (orbitAffineNormCut G N u W hW : G.U.left.Opens) := by
  rw [orbitAffineNormCut, affineNormCutOfSection_eq_normCut G N hN]
  exact normCutOfNorm_isOpenInvariant G N hN W (orbitSection G u W hW)

end AlgebraicGeometry.GroupoidScheme.AffineOpenConstruction

namespace AlgebraicGeometry.GroupoidScheme.AffineOpenConstruction

variable {S : Scheme.{u}} (G : GroupoidScheme S)
  [IsFiniteLocallyFree G.s.left] [IsFiniteLocallyFree G.t.left]

/-- The norm section `g = Norm_s(t♯f)` on the saturation complement of `W`.
The norm is constructed from the original finite local bases of the source morphism. -/
def finiteLocallyFreeNormSection (W : G.U.left.Opens) (f : Γ(G.U.left, W)) :
    Γ(G.U.left, invariantInterior G W) :=
  Scheme.finiteLocallyFreeNormApp G.s.left (invariantInterior G W) (targetSection G W f)

/-- The actual nonvanishing locus of the finite locally free norm section. -/
def finiteLocallyFreeNormCut (W : G.U.left.Opens) (f : Γ(G.U.left, W)) : G.U.left.Opens :=
  G.U.left.basicOpen (finiteLocallyFreeNormSection G W f)

/-- A determinantal norm is nonzero precisely when the pulled-back section is nonzero
at every point of the source fibre. -/
theorem mem_finiteLocallyFreeNormCut_iff (W : G.U.left.Opens) (f : Γ(G.U.left, W))
    (x : G.U.left) :
    x ∈ finiteLocallyFreeNormCut G W f ↔
      x ∈ invariantInterior G W ∧
        ∀ r : G.R.left, G.s.left r = x → G.t.left r ∈ G.U.left.basicOpen f := sorry

/-- The identity arrow puts the norm cut inside the original principal open. -/
theorem finiteLocallyFreeNormCut_le_basicOpen (W : G.U.left.Opens)
    (f : Γ(G.U.left, W)) : finiteLocallyFreeNormCut G W f ≤ G.U.left.basicOpen f := by
  intro x hx
  have hs : G.s.left (G.e.left x) = x := by
    simpa using congrArg (fun f ↦ f.left x) G.identity_source
  have ht : G.t.left (G.e.left x) = x := by
    simpa using congrArg (fun f ↦ f.left x) G.identity_target
  simpa [ht] using ((mem_finiteLocallyFreeNormCut_iff G W f x).mp hx).2 (G.e.left x) hs

/-- The invariant affine neighbourhood of 03JE. Finite prime avoidance supplies `f`;
the finite locally free norm supplies `g`. Restricting `g` to the already affine `D(f)`
gives an actual affine basic open before any norm-cut identification is used. -/
def invariantAffineNeighbourhood (x : G.U.left) (W : G.U.left.affineOpens)
    (hW : G.t.left '' (G.s.left ⁻¹' {x}) ⊆ W) : G.U.left.affineOpens :=
  let f := orbitSection G x W hW
  let g := G.U.left.presheaf.map (homOfLE (orbitSection_spec G x W hW).2).op
    (finiteLocallyFreeNormSection G W f)
  ⟨G.U.left.basicOpen g, (W.2.basicOpen f).basicOpen g⟩

/-- The neighbourhood is the nonvanishing locus of the constructed norm on `W′`. -/
theorem invariantAffineNeighbourhood_eq_normCut (x : G.U.left) (W : G.U.left.affineOpens)
    (hW : G.t.left '' (G.s.left ⁻¹' {x}) ⊆ W) :
    (invariantAffineNeighbourhood G x W hW : G.U.left.Opens) =
      finiteLocallyFreeNormCut G W (orbitSection G x W hW) := by
  change G.U.left.basicOpen
      (G.U.left.presheaf.map (homOfLE (orbitSection_spec G x W hW).2).op
        (finiteLocallyFreeNormSection G W (orbitSection G x W hW))) = _
  rw [G.U.left.basicOpen_res]
  exact inf_eq_right.mpr (finiteLocallyFreeNormCut_le_basicOpen G W _)

/-- The resulting neighbourhood lies in the caller's affine open. -/
theorem invariantAffineNeighbourhood_le (x : G.U.left) (W : G.U.left.affineOpens)
    (hW : G.t.left '' (G.s.left ⁻¹' {x}) ⊆ W) :
    (invariantAffineNeighbourhood G x W hW : G.U.left.Opens) ≤ W :=
  (G.U.left.basicOpen_le _).trans (G.U.left.basicOpen_le _)

/-- The original point belongs to its constructed invariant affine neighbourhood. -/
theorem mem_invariantAffineNeighbourhood (x : G.U.left) (W : G.U.left.affineOpens)
    (hW : G.t.left '' (G.s.left ⁻¹' {x}) ⊆ W) :
    x ∈ (invariantAffineNeighbourhood G x W hW : G.U.left.Opens) := by
  rw [invariantAffineNeighbourhood_eq_normCut, mem_finiteLocallyFreeNormCut_iff]
  have hs : G.s.left (G.e.left x) = x := by
    simpa using congrArg (fun f ↦ f.left x) G.identity_source
  have ht : G.t.left (G.e.left x) = x := by
    simpa using congrArg (fun f ↦ f.left x) G.identity_target
  refine ⟨orbit_subset_invariantInterior G x W hW ⟨G.e.left x, hs, ht⟩, ?_⟩
  intro r hr
  exact (orbitSection_spec G x W hW).1 ⟨r, hr, rfl⟩

/-- The norm nonvanishing condition is preserved by composition of groupoid arrows. -/
theorem invariantAffineNeighbourhood_isOpenInvariant (x : G.U.left)
    (W : G.U.left.affineOpens) (hW : G.t.left '' (G.s.left ⁻¹' {x}) ⊆ W) :
    G.toPreRelation.IsOpenInvariant (invariantAffineNeighbourhood G x W hW : G.U.left.Opens) := by
  rw [invariantAffineNeighbourhood_eq_normCut]
  let f := orbitSection G x W hW
  have hsP : G.toPreRelation.s = G.s := by
    change Limits.prod.lift G.t G.s ≫ Limits.prod.snd = G.s
    exact Limits.prod.lift_snd G.t G.s
  have htP : G.toPreRelation.t = G.t := by
    change Limits.prod.lift G.t G.s ≫ Limits.prod.fst = G.t
    exact Limits.prod.lift_fst G.t G.s
  change Set.MapsTo _ _ _
  rw [hsP, htP]
  intro r hr
  have hPullback :
      IsPullback (Limits.pullback.fst G.s G.t).left
        (Limits.pullback.snd G.s G.t).left G.s.left G.t.left := by
    simpa using (IsPullback.of_hasPullback G.s G.t).map (Over.forget S)
  obtain ⟨hrW, hrnonzero⟩ := (mem_finiteLocallyFreeNormCut_iff G W f (G.s.left r)).mp hr
  apply (mem_finiteLocallyFreeNormCut_iff G W f (G.t.left r)).mpr
  constructor
  · apply (mem_invariantInterior G W _).mpr
    rintro ⟨q, hqW, hqt⟩
    have hi_source : G.s.left (G.i.left r) = G.t.left r := by
      simpa using congrArg (fun f ↦ f.left r) G.inverse_source
    have hi_target : G.t.left (G.i.left r) = G.s.left r := by
      simpa using congrArg (fun f ↦ f.left r) G.inverse_target
    obtain ⟨p, hp_fst, hp_snd⟩ := Scheme.exists_preimage_of_isPullback hPullback
      (G.i.left r) q (hi_source.trans hqt.symm)
    have hs : G.s.left (G.c.left p) = G.s.left q := by
      simpa [hp_snd] using congrArg (fun f ↦ f.left p) G.comp_source
    have ht : G.t.left (G.c.left p) = G.s.left r := by
      simpa [hp_fst, hi_target] using congrArg (fun f ↦ f.left p) G.comp_target
    exact hrW ⟨G.c.left p, by simpa [Set.mem_preimage, hs] using hqW, ht⟩
  · intro q hqs
    obtain ⟨p, hp_fst, hp_snd⟩ := Scheme.exists_preimage_of_isPullback hPullback q r hqs
    have hs : G.s.left (G.c.left p) = G.s.left r := by
      simpa [hp_snd] using congrArg (fun f ↦ f.left p) G.comp_source
    have ht : G.t.left (G.c.left p) = G.t.left q := by
      simpa [hp_fst] using congrArg (fun f ↦ f.left p) G.comp_target
    simpa [ht] using hrnonzero (G.c.left p) hs

/-- The affine identification is obtained from two proved basic-open affineness results.
Neither a norm property nor an admitted affineness or invertibility certificate supplies data. -/
def invariantAffineNeighbourhoodPresentation (x : G.U.left) (W : G.U.left.affineOpens)
    (hW : G.t.left '' (G.s.left ⁻¹' {x}) ⊆ W) :
    Spec Γ(G.U.left, invariantAffineNeighbourhood G x W hW) ≅
      (invariantAffineNeighbourhood G x W hW : Scheme) :=
  (invariantAffineNeighbourhood G x W hW).2.isoSpec.symm

/-- The affine Spec chart into the object scheme. -/
def invariantAffineNeighbourhoodChart (x : G.U.left) (W : G.U.left.affineOpens)
    (hW : G.t.left '' (G.s.left ⁻¹' {x}) ⊆ W) :
    Spec Γ(G.U.left, invariantAffineNeighbourhood G x W hW) ⟶ G.U.left :=
  (invariantAffineNeighbourhoodPresentation G x W hW).hom ≫
    (invariantAffineNeighbourhood G x W hW).1.ι

end AlgebraicGeometry.GroupoidScheme.AffineOpenConstruction
