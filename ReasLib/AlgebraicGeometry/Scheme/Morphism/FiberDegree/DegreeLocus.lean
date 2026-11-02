/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiberDegree.Filtration

/-!
# Degree-at-least loci of scheme morphisms

This file defines fibre-degree lower bounds and the corresponding open loci for flat, locally
finitely presented, separated, locally quasi-finite morphisms of schemes.
-/

@[expose] public section

open CategoryTheory Limits TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry
namespace Scheme.Hom

variable {X S Z : Scheme.{u}}

/-- A scheme over a field has degree at least `d` if it contains a finite locally free open
subscheme whose rank is at least `d`. -/
def HasDegreeAtLeast {k : Type u} [Field k]
    (p : Z ⟶ Spec (CommRingCat.of k)) (d : ℕ) : Prop :=
  ∃ (U : Z.Opens) (r : ℕ), IsFiniteLocallyFreeOfRank (U.ι ≫ p) r ∧ d ≤ r

/-- The finite-open-subscheme characterization of having degree at least `d`. -/
theorem hasDegreeAtLeast_iff {k : Type u} [Field k]
    (p : Z ⟶ Spec (CommRingCat.of k)) (d : ℕ) :
    p.HasDegreeAtLeast d ↔
      ∃ (U : Z.Opens) (r : ℕ), IsFiniteLocallyFreeOfRank (U.ι ≫ p) r ∧ d ≤ r :=
  Iff.rfl

namespace HasDegreeAtLeast

set_option backward.isDefEq.respectTransparency false in
/-- Transport finite local rank using the same local bases and their images. -/
private theorem moduleRank_of_iso {S : Scheme.{u}} {M N : S.Modules}
    (e : M ≅ N) (r : ℕ) (h : Scheme.Modules.IsFiniteLocallyFreeOfRank r M) :
    Scheme.Modules.IsFiniteLocallyFreeOfRank r N := by
  letI : ∀ U : S.Opens,
      HasWeakSheafify ((Opens.grothendieckTopology S).over U) AddCommGrpCat.{u} :=
    fun U ↦ inferInstance
  letI : ∀ U : S.Opens,
      ((Opens.grothendieckTopology S).over U).WEqualsLocallyBijective AddCommGrpCat.{u} :=
    fun U ↦ inferInstance
  obtain ⟨q, hq⟩ := h.exists_rank_data
  letI := hq
  let q' : SheafOfModules.LocalGeneratorsData N :=
    { I := q.I
      X := q.X
      coversTop := q.coversTop
      generators i := (q.generators i).ofEpi (e.hom.over (q.X i)) }
  have hq' : q'.IsFreeOfRank r :=
    { isIso i := by
        change IsIso ((q.generators i).ofEpi (e.hom.over (q.X i))).π
        rw [SheafOfModules.GeneratingSections.ofEpi_π]
        infer_instance
      equivFin i := hq.equivFin i }
  have hfinite : q'.IsFiniteType := by
    constructor
    intro i
    obtain ⟨a⟩ := hq.equivFin i
    exact ⟨Finite.of_equiv (Fin r) a.symm⟩
  exact
    { exists_data := ⟨q', hq'.toIsLocallyFreeData, hfinite⟩
      exists_rank_data := ⟨q', hq'⟩ }

set_option backward.isDefEq.respectTransparency false in
/-- A finite locally free scheme over a field has degree at least every lower bound on its
rank. -/
theorem of_isFiniteLocallyFreeOfRank {k : Type u} [Field k]
    {p : Z ⟶ Spec (CommRingCat.of k)} {d r : ℕ}
    (h : IsFiniteLocallyFreeOfRank p r) (hdr : d ≤ r) : p.HasDegreeAtLeast d := by
  refine ⟨⊤, r, ?_, hdr⟩
  let i := (⊤ : Z.Opens).ι
  letI : IsIso i := inferInstanceAs (IsIso Z.topIso.hom)
  letI := h
  let e : p.pushforwardStructureModule ≅ (i ≫ p).pushforwardStructureModule :=
    (SheafOfModules.fullyFaithfulForget _).preimageIso <|
      PresheafOfModules.isoMk (fun U ↦ ModuleCat.isoMk
        ((forget₂ CommRingCat RingCat ⋙ forget₂ _ AddCommGrpCat).mapIso
          (asIso (i.app (p ⁻¹ᵁ U.unop)))) (by
            intro a
            ext x
            exact (map_mul (i.app (p ⁻¹ᵁ U.unop)).hom _ _).symm)) (by
              intro U V g
              ext x
              exact congr($(i.naturality ((Opens.map p.base).map g.unop).op) x))
  have hrank := moduleRank_of_iso e r h.pushforward_isFiniteLocallyFreeOfRank
  exact
    { toIsFiniteLocallyFree :=
        { toIsAffineHom := inferInstance
          pushforward_isFiniteLocallyFree := hrank.toIsFiniteLocallyFree }
      pushforward_isFiniteLocallyFreeOfRank := hrank }

/-- Having degree at least `d` implies having degree at least every `e ≤ d`. -/
theorem mono {k : Type u} [Field k] {p : Z ⟶ Spec (CommRingCat.of k)}
    {d e : ℕ} (h : p.HasDegreeAtLeast d) (hed : e ≤ d) :
    p.HasDegreeAtLeast e := by
  obtain ⟨U, r, hr, hdr⟩ := h
  exact ⟨U, r, hr, hed.trans hdr⟩

end HasDegreeAtLeast

/-- The set of target points whose residue-field fibres have degree at least `d`. -/
def degreeAtLeastLocus (f : X ⟶ S) (d : ℕ) : Set S :=
  {s | (f.fiberToSpecResidueField s).HasDegreeAtLeast d}

/-- Membership in the degree-at-least locus is the intrinsic degree condition on the
residue-field fibre. -/
theorem mem_degreeAtLeastLocus (f : X ⟶ S) (d : ℕ) (s : S) :
    s ∈ f.degreeAtLeastLocus d ↔
      (f.fiberToSpecResidueField s).HasDegreeAtLeast d :=
  Iff.rfl

/-- For a flat, locally finitely presented, separated, locally quasi-finite morphism, the
degree-at-least locus is open. -/
theorem degreeAtLeastLocus_isOpen (f : X ⟶ S) [Flat f]
    [LocallyOfFinitePresentation f] [IsSeparated f] [LocallyQuasiFinite f] (d : ℕ) :
    IsOpen (f.degreeAtLeastLocus d) := sorry

/-- The canonical open subscheme of points whose fibres have degree at least `d`. -/
def degreeAtLeastOpen (f : X ⟶ S) [Flat f] [LocallyOfFinitePresentation f]
    [IsSeparated f] [LocallyQuasiFinite f] (d : ℕ) : S.Opens :=
  ⟨f.degreeAtLeastLocus d, f.degreeAtLeastLocus_isOpen d⟩

/-- Membership in the canonical open is the intrinsic degree condition on the
residue-field fibre. -/
theorem mem_degreeAtLeastOpen (f : X ⟶ S) [Flat f] [LocallyOfFinitePresentation f]
    [IsSeparated f] [LocallyQuasiFinite f] (d : ℕ) (s : S) :
    s ∈ f.degreeAtLeastOpen d ↔
      (f.fiberToSpecResidueField s).HasDegreeAtLeast d :=
  Iff.rfl

/-- The degree-at-least-zero open is the whole target. -/
theorem degreeAtLeastOpen_zero (f : X ⟶ S) [Flat f] [LocallyOfFinitePresentation f]
    [IsSeparated f] [LocallyQuasiFinite f] :
    f.degreeAtLeastOpen 0 = ⊤ := sorry

/-- The canonical degree-at-least opens form a decreasing sequence. -/
theorem degreeAtLeastOpen_antitone (f : X ⟶ S) [Flat f]
    [LocallyOfFinitePresentation f] [IsSeparated f] [LocallyQuasiFinite f] :
    Antitone f.degreeAtLeastOpen := by
  intro d e hde s hs
  exact HasDegreeAtLeast.mono hs hde

/-- A field-valued point factors through the degree-at-least open exactly when the
corresponding pullback has degree at least `d`. -/
theorem factorsThrough_degreeAtLeastOpen_iff (f : X ⟶ S) [Flat f]
    [LocallyOfFinitePresentation f] [IsSeparated f] [LocallyQuasiFinite f]
    {k : Type u} [Field k] (g : Spec (CommRingCat.of k) ⟶ S) (d : ℕ) :
    (∃ lift : Spec (CommRingCat.of k) ⟶ (f.degreeAtLeastOpen d).toScheme,
      lift ≫ (f.degreeAtLeastOpen d).ι = g) ↔
      (pullback.snd f g).HasDegreeAtLeast d := sorry

end Scheme.Hom
end AlgebraicGeometry
