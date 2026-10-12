/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.FieldTheory.SeparableClosure
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import ReasLib.FieldTheory.Galois.IntegralClosure.ResidueField
public import ReasLib.RingTheory.Ideal.Inertia

@[expose] public section

open scoped Pointwise
open Ideal IsLocalRing Ideal.ResidueField.Invariant

universe u v w

namespace integralClosure.SepClosure

variable {A : Type u} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
variable (K : Type v) [Field K] [Algebra A K] [IsFractionRing A K]
variable (Ksep : Type w) [Field Ksep] [Algebra A Ksep] [Algebra K Ksep]
  [IsScalarTower A K Ksep] [IsSepClosure K Ksep]

/-- The separable closure of the base residue field inside the residue field of a maximal
branch of the integral closure. -/
noncomputable abbrev residueSep (m : Ideal (integralClosure A Ksep)) [m.IsMaximal] : Type w :=
  -- Local instance justification (defeq pin): the separable-closure subtype uses the canonical base-to-branch residue algebra.
  letI := integralClosure.ResidueField.algebraOfBase m
  separableClosure (maximalIdeal A).ResidueField m.ResidueField

include K

/-- The residue field of a maximal branch in the integral closure in a separable closure of
the fraction field is an algebraic closure of the base residue field. -/
theorem isAlgClosure_residueField (m : Ideal (integralClosure A Ksep)) [m.IsMaximal] :
    -- Local instance justification (defeq pin): the algebraic-closure assertion concerns the canonical base-to-branch residue algebra.
    letI := integralClosure.ResidueField.algebraOfBase m
    IsAlgClosure (maximalIdeal A).ResidueField m.ResidueField := sorry

/-- The decomposition group acts on the separable closure of the base residue field by
restriction of its canonical action on the branch residue field. -/
noncomputable def residueGaloisHom (m : Ideal (integralClosure A Ksep)) [m.IsMaximal] :
    -- Local instance justification (defeq pin): the residue Galois group is formed over the canonical base-to-branch residue algebra used to define residueSep.
    letI := integralClosure.ResidueField.algebraOfBase m
    MulAction.stabilizer Gal(Ksep/K) m →*
      Gal(residueSep Ksep m / (maximalIdeal A).ResidueField) :=
  -- Local instance justification (defeq pin): restriction uses the same canonical residue algebra as residueSep and stabilizerHom.
  letI := integralClosure.ResidueField.algebraOfBase m
  MonoidHom.mk'
    (fun σ ↦ AlgEquiv.separableClosure (stabilizerHom Gal(Ksep/K) (maximalIdeal A) m σ))
    sorry

/-- The residue Galois action evaluates as the restriction of the branch residue action. -/
theorem residueGaloisHom_apply (m : Ideal (integralClosure A Ksep)) [m.IsMaximal]
    (σ : MulAction.stabilizer Gal(Ksep/K) m) (x : residueSep Ksep m) :
    (residueGaloisHom K Ksep m σ x).1 =
      stabilizerHom Gal(Ksep/K) (maximalIdeal A) m σ x.1 := sorry

/-- The kernel of the decomposition-group action on the residue separable closure is the
inertia subgroup inside the decomposition group. -/
theorem residueGaloisHom_ker (m : Ideal (integralClosure A Ksep)) [m.IsMaximal] :
    (residueGaloisHom K Ksep m).ker =
      m.inertia (MulAction.stabilizer Gal(Ksep/K) m) := sorry

/-- The decomposition group surjects onto the Galois group of the residue separable closure. -/
theorem residueGaloisHom_surjective (m : Ideal (integralClosure A Ksep)) [m.IsMaximal] :
    Function.Surjective (residueGaloisHom K Ksep m) := sorry

end integralClosure.SepClosure
