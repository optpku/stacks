module

public import Mathlib.AlgebraicGeometry.Fiber
public import ReasLib.AlgebraicGeometry.PuncturedSpectrum
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Modification
public import ReasLib.AlgebraicGeometry.Scheme.Normal
public import ReasLib.RingTheory.Normal.RationalSingularity

/-!
# Rational-singularity situations

This file packages the standard setup for a rational surface singularity and a
normal modification together with an enumeration of the special-fibre
components.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

namespace AlgebraicGeometry.RationalSingularity

/-- The data of a rational surface singularity and a normal modification over its spectrum. -/
structure Situation (A : Type u) [CommRing A] [IsDomain A]
    [IsRationalSingularity A] where
  /-- The scheme carrying the modification. -/
  X : Scheme.{u}
  /-- The morphism from the modified scheme to the affine base. -/
  f : X ⟶ Spec (.of A)
  /-- The morphism is a modification. -/
  modificationEvidence : IsModification f
  /-- The modified scheme is normal. -/
  normality : X.isNormal
  /-- The number of irreducible components of the special fibre. -/
  r : ℕ
  /-- An enumeration of the irreducible components of the special fibre. -/
  componentEnumeration :
    Fin r ≃ irreducibleComponents (f.fiber (IsLocalRing.closedPoint A))

namespace Situation

variable (A : Type u) [CommRing A] [IsDomain A] [IsRationalSingularity A]

/-- Construct a situation from a modification, its normality, and its special-fibre components. -/
def of (X : Scheme.{u}) (f : X ⟶ Spec (.of A)) [IsModification f]
    (normal : X.isNormal) (r : ℕ)
    (components : Fin r ≃ irreducibleComponents (f.fiber (IsLocalRing.closedPoint A))) :
  Situation A where
  X := X
  f := f
  modificationEvidence := inferInstance
  normality := normal
  r := r
  componentEnumeration := components

/-- The domain structure on the ring underlying a rational-singularity situation. -/
def domain (S : Situation A) : IsDomain A := inferInstance

/-- The rational-singularity structure on the ring underlying a situation. -/
def rationalSingularity (S : Situation A) : IsRationalSingularity A := inferInstance

/-- The maximal ideal of the ring underlying a rational-singularity situation. -/
noncomputable def maximalIdeal (S : Situation A) : Ideal A := IsLocalRing.maximalIdeal A

/-- The residue field of the ring underlying a rational-singularity situation. -/
abbrev residueField (S : Situation A) : Type u := IsLocalRing.ResidueField A

/-- The affine scheme underlying the ring of a rational-singularity situation. -/
noncomputable abbrev scheme (S : Situation A) : Scheme.{u} := Spec (.of A)

/-- The closed point of the affine scheme underlying a rational-singularity situation. -/
noncomputable def closedPoint (S : Situation A) : PrimeSpectrum A :=
  IsLocalRing.closedPoint A

/-- The punctured spectrum of the affine scheme underlying a rational-singularity situation. -/
noncomputable abbrev puncturedSpectrum (S : Situation A) : Scheme.{u} :=
  PuncturedSpectrum.scheme A

/-- The modification morphism stored in a rational-singularity situation. -/
def modification (S : Situation A) : IsModification S.f := S.modificationEvidence

/-- The normality evidence stored in a rational-singularity situation. -/
def normal (S : Situation A) : S.X.isNormal := S.normality

/-- The enumeration of special-fibre components stored in a situation. -/
def components (S : Situation A) :
    Fin S.r ≃ irreducibleComponents (S.f.fiber (IsLocalRing.closedPoint A)) :=
  S.componentEnumeration

end Situation

end AlgebraicGeometry.RationalSingularity
