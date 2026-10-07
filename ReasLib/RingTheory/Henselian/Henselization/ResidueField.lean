module

public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.Henselian.Henselization

@[expose] public section

/-!
# Residue-field scalar transport along henselizations

The residue-field equivalence of a henselization transports scalar structures
on a target commutative algebra.  The transported algebra is deliberately a named
non-instance: distinct henselizations or residue-field identifications can
give competing algebra structures on the same target.

@stack 04GN
-/

noncomputable section

open IsLocalRing

universe u v w

namespace IsHenselizationOf.ResidueField

variable {R : Type u} [CommRing R] [IsLocalRing R]
variable {Rh : Type v} [CommRing Rh] [Algebra R Rh] [IsHenselizationOf R Rh]

/-- Tag 04GN: transport a residue-field algebra structure backwards along the
canonical residue-field equivalence of a henselization.  This is not a global
instance because the transport depends on the chosen henselization. -/
@[stacks 04GN "henselization residue-field scalar transport", implicit_reducible]
noncomputable def transportAlgebra
    {K : Type w} [CommRing K] [Algebra (ResidueField R) K] :
    Algebra (ResidueField Rh) K :=
  Algebra.compHom K (IsHenselizationOf.residueFieldEquiv (R := R) (S := Rh)).symm.toRingHom

/-- Tag 04GN: the scalar map of `transportAlgebra` is the original scalar map
precomposed with the inverse henselization residue-field equivalence. -/
@[stacks 04GN "henselization transported residue-field scalar map"]
theorem algebraMap_transportAlgebra
    {K : Type w} [CommRing K] [Algebra (ResidueField R) K] :
    letI : Algebra (ResidueField Rh) K :=
      transportAlgebra (R := R) (Rh := Rh)
    algebraMap (ResidueField Rh) K =
      (algebraMap (ResidueField R) K).comp
        (IsHenselizationOf.residueFieldEquiv (R := R) (S := Rh)).symm.toRingHom := sorry

/-- Tag 04GN: a separable residue-field extension remains separable after
transporting its scalar structure along a henselization. -/
@[stacks 04GN "henselization transported residue-field separability"]
theorem isSeparable_transportAlgebra
    {K : Type w} [Field K] [Algebra (ResidueField R) K]
    [Algebra.IsSeparable (ResidueField R) K] :
    letI : Algebra (ResidueField Rh) K :=
      transportAlgebra (R := R) (Rh := Rh)
    Algebra.IsSeparable (ResidueField Rh) K := sorry

/-- Tag 04GN: an algebraic residue-field extension remains algebraic after
transporting its scalar structure along a henselization. -/
@[stacks 04GN "henselization transported residue-field algebraicity"]
theorem isAlgebraic_transportAlgebra
    {K : Type w} [Field K] [Algebra (ResidueField R) K]
    [Algebra.IsAlgebraic (ResidueField R) K] :
    letI : Algebra (ResidueField Rh) K :=
      transportAlgebra (R := R) (Rh := Rh)
    Algebra.IsAlgebraic (ResidueField Rh) K := sorry

/-- Tag 04GN: a separable closure of the original residue field is a separable
closure after transporting scalars along a henselization. -/
@[stacks 04GN "henselization transported residue-field separable closure"]
theorem isSepClosure_transportAlgebra
    {K : Type w} [Field K] [Algebra (ResidueField R) K]
    [IsSepClosure (ResidueField R) K] :
    letI : Algebra (ResidueField Rh) K :=
      transportAlgebra (R := R) (Rh := Rh)
    IsSepClosure (ResidueField Rh) K := sorry

end IsHenselizationOf.ResidueField
