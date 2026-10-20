/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.LocalRing.ResidueField.Polynomial
public import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed
public import Mathlib.RingTheory.Localization.Integral
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.LocalRing.ResidueField.MaximalIdeal
public import ReasLib.RingTheory.Polynomial.Lifting
public import ReasLib.RingTheory.RingHom.Local.MaximalIdeal

@[expose] public section

/-!
# Polynomial local extensions

This leaf names the prime obtained by extending the maximal ideal of a local
ring to a one-variable polynomial ring.  It is the canonical owner for the
localization used to realize a transcendental residue-field extension.
-/

universe u v

namespace Polynomial.Local

/-- A monic polynomial over the residue field of a local ring lifts to a
monic polynomial over the local ring. -/
theorem exists_monic_lift_of_residueField
    (A : Type u) [CommRing A] [IsLocalRing A]
    (g : Polynomial (IsLocalRing.ResidueField A)) (hg : g.Monic) :
    ∃ f : Polynomial A, f.Monic ∧
      f.map (algebraMap A (IsLocalRing.ResidueField A)) = g :=
  Polynomial.exists_monic_lift_of_surjective
    (algebraMap A (IsLocalRing.ResidueField A)) IsLocalRing.residue_surjective g hg

/-- An integral element over `κ(p)` has a denominator-cleared, monic minimal
polynomial lift over `R`, after scaling the element by a nonzero member of
`p`.  The primitive-element and generation hypotheses used by applications
are intentionally absent from this local polynomial owner. -/
theorem exists_monic_lift_scaled_minpoly
    {R : Type u} [CommRing R] (p : Ideal R) [p.IsPrime]
    {L : Type v} [Field L] [Algebra p.ResidueField L]
    (β : L) (hβ : IsIntegral p.ResidueField β) :
    ∃ s : p.primeCompl, ∃ f : Polynomial R, f.Monic ∧
      f.map (algebraMap R p.ResidueField) =
        (minpoly p.ResidueField β).scaleRoots
          (algebraMap R p.ResidueField s.1) := sorry

/-- The extension of the maximal ideal of a local ring to its polynomial
ring. -/
noncomputable abbrev maximalIdealExtension (A : Type u) [CommRing A] [IsLocalRing A] :
    Ideal (Polynomial A) :=
  Ideal.map Polynomial.C (IsLocalRing.maximalIdeal A)

/-- The polynomial extension of a local maximal ideal lies over that maximal
ideal. -/
instance maximalIdealExtension_liesOver (A : Type u) [CommRing A] [IsLocalRing A] :
    (maximalIdealExtension A).LiesOver (IsLocalRing.maximalIdeal A) := sorry

/-- The localization of `A[X]` at the extension of the maximal ideal of the
local ring `A`. -/
abbrev atMaximal (A : Type u) [CommRing A] [IsLocalRing A] : Type u :=
  Localization.AtPrime (maximalIdealExtension A)

/-- The canonical map from a local ring to its polynomial localization at the
extended maximal ideal preserves maximal ideals. -/
theorem mapsMaximalIdeal (A : Type u) [CommRing A] [IsLocalRing A] :
    RingHom.MapsMaximalIdeal (algebraMap A (atMaximal A)) := sorry

/-- The canonical map from a local ring to its polynomial localization at the
extended maximal ideal is a local ring homomorphism. -/
instance instIsLocalHom (A : Type u) [CommRing A] [IsLocalRing A] :
    IsLocalHom (algebraMap A (atMaximal A)) := sorry

/-- The localization at the extended maximal ideal is flat over its local base. -/
theorem flat (A : Type u) [CommRing A] [IsLocalRing A] :
    (algebraMap A (atMaximal A)).Flat := sorry

/-- Reduction of a polynomial over a local ring to its residue field. -/
noncomputable abbrev reduction {A : Type u} [CommRing A] [IsLocalRing A]
    (f : Polynomial A) : Polynomial (IsLocalRing.ResidueField A) :=
  f.map (algebraMap A (IsLocalRing.ResidueField A))

/-- The residue field of `A[X]` localized at the extended maximal ideal is
the rational-function field of the residue field of `A`. -/
noncomputable def residueFieldEquiv (A : Type u) [CommRing A] [IsLocalRing A] :
    IsLocalRing.ResidueField (atMaximal A) ≃+*
      RatFunc (IsLocalRing.ResidueField A) := by
  -- Mathlib intentionally leaves this localization algebra non-global to avoid diamonds. Pin the
  -- canonical map only while invoking the polynomial residue-field construction.
  letI : Algebra (Localization.AtPrime (IsLocalRing.maximalIdeal A))
      (Localization.AtPrime (maximalIdealExtension A)) :=
    Localization.AtPrime.algebraOfLiesOver
      (IsLocalRing.maximalIdeal A) (maximalIdealExtension A)
  letI : Localization.AtPrime.IsLiesOverAlgebra
      (IsLocalRing.maximalIdeal A) (maximalIdealExtension A) := ⟨rfl⟩
  let eIdeal : (maximalIdealExtension A).ResidueField ≃+*
      RatFunc (IsLocalRing.maximalIdeal A).ResidueField :=
    (residueFieldMapCAlgEquiv (I := IsLocalRing.maximalIdeal A)
      (J := maximalIdealExtension A) rfl).toRingEquiv
  let eResidue : RatFunc (IsLocalRing.maximalIdeal A).ResidueField ≃+*
      RatFunc (IsLocalRing.ResidueField A) :=
    IsFractionRing.ringEquivOfRingEquiv
      (Polynomial.mapEquiv
        (IsLocalRing.ResidueField.maximalIdealAlgEquiv A).symm.toRingEquiv)
  simpa [atMaximal, Ideal.ResidueField] using eIdeal.trans eResidue

/-- `residueFieldEquiv` sends the residue class of a coefficient to the
corresponding constant rational function. -/
@[simp]
theorem residueFieldEquiv_apply_residue
    (A : Type u) [CommRing A] [IsLocalRing A] (a : A) :
    residueFieldEquiv A
        (IsLocalRing.residue (atMaximal A)
          (algebraMap A (atMaximal A) a)) =
      algebraMap (Polynomial (IsLocalRing.ResidueField A))
        (RatFunc (IsLocalRing.ResidueField A))
        (Polynomial.C (IsLocalRing.residue A a)) := sorry

end Polynomial.Local
