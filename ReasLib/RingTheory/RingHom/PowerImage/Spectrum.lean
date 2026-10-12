/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.RingHom.PowerImage.Integral
public import ReasLib.RingTheory.RingHom.PowerImage.BaseChange
public import ReasLib.RingTheory.RingHom.Spectrum.BaseChange
public import ReasLib.RingTheory.RingHom.Subintegral
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Spectral consequences of power-image generation

@stack 0EUH

This leaf owns the residue-field and prime-spectrum consequences of positive
coprime power-image conditions. It deliberately contains no chapter imports;
source entries should only package these owners with their textbook labels.
-/

@[expose] public section

open PrimeSpectrum

universe u v w

namespace RingHom

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]

namespace PowerImage.Pair

/-- Two positive coprime power-image generators make every induced residue-field map bijective. -/
theorem residueField_map_bijective
    {f : R →+* S} {m n : ℕ} (hgen : Pair.IsGenerated f m n)
    (hm : 0 < m) (hn : 0 < n) (hcop : Nat.Coprime m n)
    (q : PrimeSpectrum S) :
    Function.Bijective
      (Ideal.ResidueField.map (comap f q).asIdeal q.asIdeal f rfl) := sorry

/-- Two positive coprime power-image generators give bijective maps on all target residue fields. -/
theorem mapsBijective
    {f : R →+* S} {m n : ℕ} (hgen : Pair.IsGenerated f m n)
    (hm : 0 < m) (hn : 0 < n) (hcop : Nat.Coprime m n) :
    ResidueField.MapsBijective f := sorry

/-- Two positive coprime power-image generators make the map on prime spectra injective. -/
theorem comap_injective
    {f : R →+* S} {m n : ℕ} (hgen : Pair.IsGenerated f m n)
    (hm : 0 < m) (hn : 0 < n) (hcop : Nat.Coprime m n) :
    Function.Injective (comap f) := sorry

/-- A locally nilpotent-kernel two-power-image map with positive coprime exponents induces a
homeomorphism on prime spectra. -/
theorem isHomeomorph_comap
    {f : R →+* S} {m n : ℕ} (hgen : Pair.IsGenerated f m n)
    (hker : (RingHom.ker f).IsLocallyNilpotent)
    (hm : 0 < m) (hn : 0 < n) (hcop : Nat.Coprime m n) :
    IsHomeomorph (comap f) := sorry

/-- A positive coprime two-power-image map with locally nilpotent kernel is subintegral. -/
theorem isSubintegral
    {f : R →+* S} {m n : ℕ} (hgen : Pair.IsGenerated f m n)
    (hker : (RingHom.ker f).IsLocallyNilpotent)
    (hm : 0 < m) (hn : 0 < n) (hcop : Nat.Coprime m n) :
    f.IsSubintegral := sorry

end PowerImage.Pair

namespace PowerImage.SquareCube

/-- Square/cube power-image generation makes every induced residue-field map bijective. -/
@[stacks 0EUH]
theorem residueField_map_bijective
    {f : R →+* S} (hgen : SquareCube.IsGenerated f)
    (q : PrimeSpectrum S) :
    Function.Bijective
      (Ideal.ResidueField.map (comap f q).asIdeal q.asIdeal f rfl) := sorry

/-- Square/cube power-image generation gives the bundled residue-field property. -/
@[stacks 0EUH]
theorem mapsBijective
    {f : R →+* S} (hgen : SquareCube.IsGenerated f) :
    ResidueField.MapsBijective f := sorry

/-- Square/cube power-image generation makes the map on prime spectra injective. -/
@[stacks 0EUH]
theorem comap_injective
    {f : R →+* S} (hgen : SquareCube.IsGenerated f) :
    Function.Injective (comap f) := sorry

/-- A locally nilpotent-kernel square/cube power-image map induces a homeomorphism on spectra. -/
@[stacks 0EUH]
theorem isHomeomorph_comap
    {f : R →+* S} (hgen : SquareCube.IsGenerated f)
    (hker : (RingHom.ker f).IsLocallyNilpotent) :
    IsHomeomorph (comap f) := sorry

/-- A square/cube power-image map with locally nilpotent kernel is subintegral. -/
@[stacks 0EUH]
theorem isSubintegral
    {f : R →+* S} (hgen : SquareCube.IsGenerated f)
    (hker : (RingHom.ker f).IsLocallyNilpotent) :
    f.IsSubintegral := sorry

namespace BaseChange

/-- The kernel of a square/cube power-image map remains locally nilpotent after an arbitrary
tensor-product base change. -/
@[stacks 0EUH "locally nilpotent kernel after arbitrary base change"]
theorem ker_isLocallyNilpotent
    {R' : Type w} [CommRing R'] (f : R →+* S) (g : R →+* R')
    (hgen : SquareCube.IsGenerated f)
    (hker : (RingHom.ker f).IsLocallyNilpotent) :
    (RingHom.ker (f.baseChange g)).IsLocallyNilpotent := sorry

/-- A square/cube power-image map with locally nilpotent kernel remains subintegral after an
arbitrary tensor-product base change. -/
@[stacks 0EUH "subintegrality after arbitrary base change"]
theorem isSubintegral
    {R' : Type w} [CommRing R'] (f : R →+* S) (g : R →+* R')
    (hgen : SquareCube.IsGenerated f)
    (hker : (RingHom.ker f).IsLocallyNilpotent) :
    (f.baseChange g).IsSubintegral := sorry

end BaseChange

end PowerImage.SquareCube

end RingHom
