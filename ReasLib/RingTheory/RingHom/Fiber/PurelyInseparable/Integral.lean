/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.RingHom.Integral
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import ReasLib.RingTheory.RingHom.Fiber.PurelyInseparable
public import ReasLib.RingTheory.RingHom.Spectrum.BaseChange
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Integral maps with purely inseparable residue fields

This leaf combines the independent integral, spectrum, and residue-field
base-change APIs when their conjunction is the natural mathematical datum.  The
individual transports remain available from their smaller owners.
-/

@[expose] public section

open PrimeSpectrum
open Topology
open scoped TensorProduct

universe u v w

namespace RingHom

namespace ResidueField

namespace MapsPurelyInseparable

/-- Lemma 10.46.9 (Tag 0BRC): an integral algebra map with injective prime-spectrum map and
purely inseparable residue-field extensions is a closed embedding on spectra, and these three
properties persist under arbitrary tensor-product base change. -/
@[stacks 0BRC]
theorem isClosedEmbedding_comap_baseChange
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    (hInt : (algebraMap R S).IsIntegral)
    (hinj : Function.Injective (comap (algebraMap R S)))
    (hres : ResidueField.MapsPurelyInseparable (algebraMap R S)) :
    IsClosedEmbedding (comap (algebraMap R S)) ∧
      ∀ {R' : Type w} [CommRing R'] [Algebra R R'],
        let f' : R' →+* R' ⊗[R] S := algebraMap R' (R' ⊗[R] S)
        f'.IsIntegral ∧ Function.Injective (comap f') ∧
          ResidueField.MapsPurelyInseparable f' := sorry

/-- Lemma 10.46.10 (Tag 0BRD): if the integral algebra map has bijective prime-spectrum map and
purely inseparable residue-field extensions, then its spectrum map is a homeomorphism; these
properties persist under arbitrary tensor-product base change. -/
@[stacks 0BRD]
theorem isHomeomorph_comap_baseChange
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    (hInt : (algebraMap R S).IsIntegral)
    (hbij : Function.Bijective (comap (algebraMap R S)))
    (hres : ResidueField.MapsPurelyInseparable (algebraMap R S)) :
    IsHomeomorph (comap (algebraMap R S)) ∧
      ∀ {R' : Type w} [CommRing R'] [Algebra R R'],
        let f' : R' →+* R' ⊗[R] S := algebraMap R' (R' ⊗[R] S)
        f'.IsIntegral ∧ Function.Bijective (comap f') ∧
          ResidueField.MapsPurelyInseparable f' := sorry

end MapsPurelyInseparable

end ResidueField

end RingHom
