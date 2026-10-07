module

public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.KrullDimension.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Module.Cohomology
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Modification
public import ReasLib.AlgebraicGeometry.Scheme.Normal
public import ReasLib.RingTheory.Normal.Local
public import ReasLib.RingTheory.Normal.Nagata
public import ReasLib.RingTheory.Normal.RegularLocal

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

/-- A rational surface singularity is a two-dimensional Nagata normal local ring for which
the first cohomology of the structure sheaf vanishes on every normal modification. -/
class IsRationalSingularity (A : Type u) [CommRing A] : Prop where
  /-- A rational surface singularity is local. -/
  isLocalRing : IsLocalRing A
  /-- A rational surface singularity is Nagata. -/
  nagataRing : NagataRing A
  /-- A rational surface singularity is normal. -/
  isNormalRing : IsNormalRing A
  /-- A rational surface singularity has Krull dimension two. -/
  dimension_eq : ringKrullDim A = 2
  /-- The first cohomology of the structure sheaf vanishes on every normal modification. -/
  h1IsZero (X : Scheme.{u}) (f : X ⟶ Spec (.of A)) [IsModification f] (hX : X.isNormal) :
    IsZero (Scheme.Modules.cohomology
      (SheafOfModules.unit X.ringCatSheaf : X.Modules) 1)

namespace IsRationalSingularity

/-- A rational surface singularity carries its canonical local-ring instance. -/
instance instIsLocalRing (A : Type u) [CommRing A] [IsRationalSingularity A] :
    IsLocalRing A := sorry

/-- A rational surface singularity carries its canonical Nagata-ring instance. -/
instance instNagataRing (A : Type u) [CommRing A] [IsRationalSingularity A] :
    NagataRing A := sorry

/-- A rational surface singularity carries its canonical normal-ring instance. -/
instance instIsNormalRing (A : Type u) [CommRing A] [IsRationalSingularity A] :
    IsNormalRing A := sorry

/-- A Nagata regular local ring of Krull dimension two defines a rational singularity. -/
theorem ofRegularLocalRing
    (A : Type u) [CommRing A] [IsRegularLocalRing A] [NagataRing A]
    (h_dimension : ringKrullDim A = 2) :
    IsRationalSingularity A := sorry

/-- The maximal-ideal completion of a rational surface singularity is again a rational
surface singularity, provided that the completion is normal. -/
instance instAdicCompletion
    (A : Type u) [CommRing A] [IsDomain A] [IsRationalSingularity A]
    [IsNormalRing (AdicCompletion (IsLocalRing.maximalIdeal A) A)] :
    IsRationalSingularity (AdicCompletion (IsLocalRing.maximalIdeal A) A) := sorry

end IsRationalSingularity

/-- The defining conditions for a rational surface singularity. -/
theorem isRationalSingularity_iff (A : Type u) [CommRing A] :
    IsRationalSingularity A ↔
      IsLocalRing A ∧ NagataRing A ∧ IsNormalRing A ∧ ringKrullDim A = 2 ∧
        ∀ (X : Scheme.{u}) (f : X ⟶ Spec (.of A)) [IsModification f], X.isNormal →
          IsZero (Scheme.Modules.cohomology
            (SheafOfModules.unit X.ringCatSheaf : X.Modules) 1) := sorry
