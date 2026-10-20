/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Generic residue fields in finite fraction-field extensions

For a compatible extension of domains with a finite-dimensional extension of
fraction fields, the residue-field extension at the generic points is finite.
-/

@[expose] public section

universe u v w

namespace Ideal.ResidueField

variable {A : Type u} {B : Type v} {L : Type w}
variable [CommRing A] [IsDomain A] [CommRing B] [IsDomain B]
variable [Field L] [Algebra A B] [Algebra A L] [Algebra B L]
variable [Algebra (FractionRing A) L]
variable [IsScalarTower A B L] [IsScalarTower A (FractionRing A) L]
variable [IsFractionRing B L] [FiniteDimensional (FractionRing A) L]

/-- If compatible domains have the same fraction-field model and
`L` is finite over `FractionRing A`, then the residue-field map at the two
generic points is finite.  The scalar algebra is scoped because it is induced
by the specified map `A → B`. -/
@[stacks 09IG "generic residue-field finiteness from a finite fraction-field extension"]
theorem moduleFinite_bot_of_finiteDimensional
    (hcomap : Ideal.comap (algebraMap A B) (⊥ : Ideal B) = (⊥ : Ideal A)) :
    let f : ((⊥ : Ideal A).ResidueField) →+* ((⊥ : Ideal B).ResidueField) :=
      Ideal.ResidueField.map (⊥ : Ideal A) (⊥ : Ideal B)
        (algebraMap A B) hcomap.symm
    -- Local instance justification (noncanonical choice): the generic residue-field algebra is
    -- determined by the specified map between the two domains.
    letI : Algebra ((⊥ : Ideal A).ResidueField) ((⊥ : Ideal B).ResidueField) :=
      f.toAlgebra
    Module.Finite ((⊥ : Ideal A).ResidueField) ((⊥ : Ideal B).ResidueField) := sorry

end Ideal.ResidueField
