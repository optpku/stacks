/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import ReasLib.Algebra.Category.ModuleCat.Tor.Notation
public import ReasLib.Algebra.Module.Injective.Hull
public import ReasLib.RingTheory.Gorenstein.Local

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped ModuleTor

universe u

namespace LinearMap.IsInjectiveHull

/-- For an injective hull `E` of the residue field of a local Gorenstein ring of
Krull dimension `d`, `Tor⁽i⁾[A](E, IsLocalRing.ResidueField A)` is zero whenever
`i ≠ d`. -/
theorem tor_isZero_of_ne_krullDim
    {A E : Type u} [CommRing A] [IsLocalRing A] [IsGorensteinLocalRing A]
    [AddCommGroup E] [Module A E] [Module.Injective A E]
    {ι : IsLocalRing.ResidueField A →ₗ[A] E} (hι : ι.IsInjectiveHull)
    (d i : ℕ) (hd : ringKrullDim A = d) (hi : i ≠ d) :
    IsZero (Tor⁽i⁾[A](E, IsLocalRing.ResidueField A)) := sorry

/-- For an injective hull `E` of the residue field of a local Gorenstein ring of
Krull dimension `d`, the degree-`d` Tor object is isomorphic to the residue
field. -/
theorem tor_iso_residueField
    {A E : Type u} [CommRing A] [IsLocalRing A] [IsGorensteinLocalRing A]
    [AddCommGroup E] [Module A E] [Module.Injective A E]
    {ι : IsLocalRing.ResidueField A →ₗ[A] E} (hι : ι.IsInjectiveHull)
    (d : ℕ) (hd : ringKrullDim A = d) :
    Nonempty
      (Tor⁽d⁾[A](E, IsLocalRing.ResidueField A) ≅
        ModuleCat.of A (IsLocalRing.ResidueField A)) := sorry

end LinearMap.IsInjectiveHull
