/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Normal.RationalSingularity

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

/- Compatibility checks for the rational-singularity API owned by ReasLib. -/
#check (@IsRationalSingularity : (A : Type u) → [CommRing A] → Prop)
#check (@IsRationalSingularity.instIsLocalRing :
  (A : Type u) → [CommRing A] → [IsRationalSingularity A] → IsLocalRing A)
#check (@IsRationalSingularity.instNagataRing :
  (A : Type u) → [CommRing A] → [IsRationalSingularity A] → NagataRing A)
#check (@IsRationalSingularity.instIsNormalRing :
  (A : Type u) → [CommRing A] → [IsRationalSingularity A] → IsNormalRing A)
#check (@isRationalSingularity_iff :
  (A : Type u) → [CommRing A] →
    IsRationalSingularity A ↔
      IsLocalRing A ∧ NagataRing A ∧ IsNormalRing A ∧ ringKrullDim A = 2 ∧
        ∀ (X : Scheme.{u}) (f : X ⟶ Spec (.of A)) [IsModification f], X.isNormal →
          IsZero (Scheme.Modules.cohomology
            (SheafOfModules.unit X.ringCatSheaf : X.Modules) 1))
