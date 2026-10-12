/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.Localization.Defs
public import ReasLib.AlgebraicGeometry.Scheme.WLocalAffine.Component

/-!
# Canonical surjections of specializing localizations

Each component localization `A_Z^~` maps onto the sections ring
`(A ⧸ I)_f` of the corresponding vanishing-pattern stratum.
-/

@[expose] public section

universe u

open AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.WLocalAffine

variable {A : Type u} [CommRing A]

/-- The canonical surjection `A_Z^~ → (A ⧸ I)_f` of lemma-localization, induced
by the structure map of `A` into the sections of `D(f) ∩ V(I)`. -/
noncomputable def toSections {E : Finset A} (p : VanishingPattern E) :
    componentAlgebra p →+* stratumSections p :=
  IsLocalization.lift (M := unitsPreimage p) (g := algebraMap A (stratumSections p))
    fun y ↦
      (IsUnit.mem_submonoid_iff _).mp
        (Submonoid.mem_comap.mp
          (y.property : y.1 ∈ (IsUnit.submonoid (stratumSections p)).comap
            (algebraMap A (stratumSections p))))

/-- The canonical map `A_Z^~ → (A ⧸ I)_f` is surjective. -/
theorem toSections_surjective {E : Finset A} (p : VanishingPattern E) :
    Function.Surjective (toSections p) :=
  sorry

end AlgebraicGeometry.Scheme.WLocalAffine
