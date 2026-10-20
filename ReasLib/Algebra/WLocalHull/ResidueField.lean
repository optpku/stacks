/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Mathlib.Topology.Connected.TotallyDisconnected
public import ReasLib.Topology.WLocal
public import ReasLib.RingTheory.RingHom.IndZariski
public import ReasLib.RingTheory.Algebraic.ResidueField
public import ReasLib.Algebra.WLocalHull.AlongClosed

/-!
# Going up along algebraic residue-field extensions of a w-local affine

If `Spec(A)` is w-local and `A → B` induces algebraic residue-field extensions,
the closed-points ideal `I` of `A` remains a closed-points locus after base
change to `B`, and the specializing localization `alongClosed B (I.map _)`
supplies the induced w-local map back to `Spec(A)`.
-/

@[expose] public section

universe u

open PrimeSpectrum

namespace Algebra.WLocalHull

variable {A : Type u} [CommRing A] (B : Type u) [CommRing B] [Algebra A B]
variable (I : Ideal A)

/-- The composite structure map `A → alongClosed B (I.map (algebraMap A B))`
inducing `p : Spec(alongClosed B (I.map (algebraMap A B))) → Spec(A)`. -/
noncomputable def alongClosedComp :
    A →+* alongClosed B (I.map (algebraMap A B)) :=
  (algebraMap B (alongClosed B (I.map (algebraMap A B)))).comp (algebraMap A B)

/-- `alongClosedComp B I` is the composite of `algebraMap A B` with the structure
map of `alongClosed B (I.map (algebraMap A B))`. -/
theorem alongClosedComp_eq :
    alongClosedComp B I =
      (algebraMap B (alongClosed B (I.map (algebraMap A B)))).comp
        (algebraMap A B) :=
  rfl

variable [WLocalSpace (PrimeSpectrum A)]

/-- If `V(I)` is the set of closed points of `Spec(A)` and residue-field
extensions of `A → B` are algebraic, then every point of
`V(I.map (algebraMap A B))` is closed in `Spec(B)`. -/
theorem zeroLocus_map_subset_closedPoints
    (hI : zeroLocus (I : Set A) = closedPoints (PrimeSpectrum A))
    (h : IsAlgebraicOnResidueFields A B) :
    zeroLocus (I.map (algebraMap A B) : Set B) ⊆
      closedPoints (PrimeSpectrum B) :=
  sorry

/-- Total disconnectedness of `V(I.map (algebraMap A B))` from the w-local
closed-points locus of `Spec(A)` and algebraic residue-field extensions. -/
instance instTotallyDisconnectedSpace_zeroLocus_map
    [Fact (zeroLocus (I : Set A) = closedPoints (PrimeSpectrum A))]
    [Fact (IsAlgebraicOnResidueFields A B)] :
    TotallyDisconnectedSpace (zeroLocus (I.map (algebraMap A B) : Set B)) :=
  sorry

/-- `Spec(alongClosed B (I.map (algebraMap A B)))` is w-local under the
hypotheses of going up along algebraic residue-field extensions. -/
theorem wLocalSpace_alongClosed_map
    (hI : zeroLocus (I : Set A) = closedPoints (PrimeSpectrum A))
    (h : IsAlgebraicOnResidueFields A B) :
    WLocalSpace (PrimeSpectrum (alongClosed B (I.map (algebraMap A B)))) :=
  sorry

/-- The canonical map `B ⧸ I.map (algebraMap A B) → alongClosed B (I.map (algebraMap A B))`
modulo the image of that ideal is bijective. -/
theorem bijective_quotientMap_alongClosed_map
    (hI : zeroLocus (I : Set A) = closedPoints (PrimeSpectrum A))
    (h : IsAlgebraicOnResidueFields A B) :
    Function.Bijective
      (Ideal.quotientMap
        ((I.map (algebraMap A B)).map
          (algebraMap B (alongClosed B (I.map (algebraMap A B)))))
        (algebraMap B (alongClosed B (I.map (algebraMap A B))))
        Ideal.le_comap_map) :=
  sorry

/-- The induced map `Spec(alongClosed B (I.map (algebraMap A B))) → Spec(A)`
is w-local. -/
instance instIsWLocalMap_comap_alongClosed
    [Fact (zeroLocus (I : Set A) = closedPoints (PrimeSpectrum A))]
    [Fact (IsAlgebraicOnResidueFields A B)] :
    IsWLocalMap (PrimeSpectrum.comap (alongClosedComp B I)) :=
  sorry

/-- The preimage of the closed points of `Spec(A)` under
`PrimeSpectrum.comap (alongClosedComp B I)` is the set of closed points of
`Spec(alongClosed B (I.map (algebraMap A B)))`. -/
theorem comap_preimage_closedPoints_alongClosed
    (hI : zeroLocus (I : Set A) = closedPoints (PrimeSpectrum A))
    (h : IsAlgebraicOnResidueFields A B) :
    PrimeSpectrum.comap (alongClosedComp B I) ⁻¹'
        closedPoints (PrimeSpectrum A) =
      closedPoints (PrimeSpectrum (alongClosed B (I.map (algebraMap A B)))) :=
  sorry

end Algebra.WLocalHull
