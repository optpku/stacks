/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
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
      ∃ (U : Z.Opens) (r : ℕ), IsFiniteLocallyFreeOfRank (U.ι ≫ p) r ∧ d ≤ r := sorry

namespace HasDegreeAtLeast

/-- A finite locally free scheme over a field has degree at least every lower bound on its
rank. -/
theorem of_isFiniteLocallyFreeOfRank {k : Type u} [Field k]
    {p : Z ⟶ Spec (CommRingCat.of k)} {d r : ℕ}
    (h : IsFiniteLocallyFreeOfRank p r) (hdr : d ≤ r) : p.HasDegreeAtLeast d := sorry

/-- Having degree at least `d` implies having degree at least every `e ≤ d`. -/
theorem mono {k : Type u} [Field k] {p : Z ⟶ Spec (CommRingCat.of k)}
    {d e : ℕ} (h : p.HasDegreeAtLeast d) (hed : e ≤ d) :
    p.HasDegreeAtLeast e := sorry

end HasDegreeAtLeast

/-- The set of target points whose residue-field fibres have degree at least `d`. -/
def degreeAtLeastLocus (f : X ⟶ S) (d : ℕ) : Set S :=
  {s | (f.fiberToSpecResidueField s).HasDegreeAtLeast d}

/-- Membership in the degree-at-least locus is the intrinsic degree condition on the
residue-field fibre. -/
theorem mem_degreeAtLeastLocus (f : X ⟶ S) (d : ℕ) (s : S) :
    s ∈ f.degreeAtLeastLocus d ↔
      (f.fiberToSpecResidueField s).HasDegreeAtLeast d := sorry

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
      (f.fiberToSpecResidueField s).HasDegreeAtLeast d := sorry

/-- The degree-at-least-zero open is the whole target. -/
theorem degreeAtLeastOpen_zero (f : X ⟶ S) [Flat f] [LocallyOfFinitePresentation f]
    [IsSeparated f] [LocallyQuasiFinite f] :
    f.degreeAtLeastOpen 0 = ⊤ := sorry

/-- The canonical degree-at-least opens form a decreasing sequence. -/
theorem degreeAtLeastOpen_antitone (f : X ⟶ S) [Flat f]
    [LocallyOfFinitePresentation f] [IsSeparated f] [LocallyQuasiFinite f] :
    Antitone f.degreeAtLeastOpen := sorry

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
