module

public import Mathlib.RingTheory.RingHom.FaithfullyFlat
public import ReasLib.FieldTheory.GeometricRegularity.FaithfullyFlat
public import ReasLib.RingTheory.Algebra.TensorProduct.RightAlgebra
public import ReasLib.RingTheory.RingHom.Fiber.BaseChange
public import ReasLib.RingTheory.Regular.RingMap
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Faithfully flat descent of regular ring maps

@stack 07NT
-/

open scoped TensorProduct Algebra.TensorProduct.Right

namespace RingHom.Regular

universe u v w

variable {A : Type u} {B : Type v} {C : Type w}
variable [CommRing A] [CommRing B] [CommRing C]

section FiberBaseChange

variable [Algebra A B] [Algebra B C]

/-- The base change of an `A`-fiber of `B` along `B → C`. -/
@[stacks 07NT "residue-field fiber base change"]
abbrev fiberBaseChange (p : PrimeSpectrum A) : Type (max u v w) :=
  (p.asIdeal.Fiber B) ⊗[B] C

/-- Faithful flatness survives base change to a residue-field fiber. -/
@[stacks 07NT "faithfully flat residue-field fiber base change"]
theorem fiber_baseChange_faithfullyFlat
    (h : (algebraMap B C).FaithfullyFlat) (p : PrimeSpectrum A) :
    Module.FaithfullyFlat (p.asIdeal.Fiber B)
      (fiberBaseChange (B := B) (C := C) p) := sorry

variable [Algebra A C] [IsScalarTower A B C]

/-- Canceling the intermediate base change identifies the iterated fiber with the composite fiber. -/
@[stacks 07NT "fiber base-change equivalence"]
noncomputable def fiber_baseChange_algEquiv (p : PrimeSpectrum A) :
    fiberBaseChange (B := B) (C := C) p ≃ₐ[p.asIdeal.ResidueField]
      p.asIdeal.Fiber C :=
  Algebra.IsPushout.cancelBaseChangeAlg A p.asIdeal.ResidueField
    B (p.asIdeal.Fiber B) C

end FiberBaseChange

variable {f : A →+* B} {g : B →+* C}

/-- Lemma 15.41.7: regularity descends from a composite along a faithfully flat second map. -/
@[stacks 07NT "faithfully flat descent of regular ring maps"]
theorem of_comp_of_faithfullyFlat
    (hgf : (g.comp f).Regular) (hg : g.FaithfullyFlat) : f.Regular := sorry

end RingHom.Regular
