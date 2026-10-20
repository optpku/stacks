/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.KrullDimension.Module
public import Mathlib.Order.WithBotTop
public import ReasLib.Algebra.Homology.DerivedCategory.LocalCohomology.CohomologicalDimension

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.DerivedCategory

universe u

namespace Ideal.LocalCohomology

variable {A : Type u} [CommRing A]

/-- A finite module has vanishing local cohomology above the Krull dimension of its support. -/
theorem isZero_above_supportDim {A M : Type u} [CommRing A] [AddCommGroup M]
    [Module A M] [Module.Finite A M] (I : Ideal A) (hI : I.FG)
    (RΓ : DerivedCategory (ModuleCat A) ⥤ DerivedCategory.IdealPowerTorsion I)
    (hRΓ : DerivedCategory.IdealPowerTorsion.inclusion I ⊣ RΓ) (i : ℤ)
    (hi : WithBot.map (WithTop.map Int.ofNat) (Module.supportDim A M) < (i : EInt)) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat A) i).obj
      (RΓ.obj (ModuleCat.single0 (ModuleCat.of A M))).obj) := sorry

/-- The local-cohomological dimension of a finitely generated ideal is bounded by the
maximum of `-1` and the Krull dimension of the ambient ring. -/
theorem dimension_le_max_ringKrullDim {A : Type u} [CommRing A]
    (I : Ideal A) (hI : I.FG) :
    (dimension I hI : EInt) ≤
      max ((-1 : ℤ) : EInt) (WithBot.map (WithTop.map Int.ofNat) (ringKrullDim A)) := sorry

/-- Over a nontrivial commutative ring, the local-cohomological dimension of a finitely
generated ideal is bounded by the Krull dimension of the ring. -/
theorem dimension_le_ringKrullDim {A : Type u} [CommRing A] [Nontrivial A]
    (I : Ideal A) (hI : I.FG) :
    (dimension I hI : EInt) ≤
      WithBot.map (WithTop.map Int.ofNat) (ringKrullDim A) := sorry

end Ideal.LocalCohomology
