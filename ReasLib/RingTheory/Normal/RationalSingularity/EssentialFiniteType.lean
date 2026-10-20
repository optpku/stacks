/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.EssentialFiniteness
public import Mathlib.RingTheory.Localization.FractionRing
public import ReasLib.RingTheory.Normal.RationalSingularity

@[expose] public section

universe u v

namespace IsRationalSingularity

/-- A two-dimensional normal local domain essentially of finite type and local over a
rational surface singularity, with the same fraction field, is a rational singularity. -/
theorem ofEssFiniteTypeOverring
    (A : Type u) [CommRing A] [IsDomain A] [IsRationalSingularity A]
    (B : Type v) [CommRing B] [IsDomain B] [Algebra A B] [IsLocalRing B]
    [IsLocalHom (algebraMap A B)] [Algebra.EssFiniteType A B]
    [Algebra B (FractionRing A)] [IsScalarTower A B (FractionRing A)]
    [IsFractionRing B (FractionRing A)] [IsNormalRing B]
    (h_dimension : ringKrullDim B = 2) :
    IsRationalSingularity B := sorry

end IsRationalSingularity
