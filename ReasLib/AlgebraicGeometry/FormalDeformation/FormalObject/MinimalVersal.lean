/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalDeformation.Predeformation
public import ReasLib.AlgebraicGeometry.FormalDeformation.Schlessinger
public import ReasLib.AlgebraicGeometry.FormalDeformation.FormalObject.Versal
public import ReasLib.AlgebraicGeometry.FormalDeformation.FormalObject.Orbits
public import ReasLib.AlgebraicGeometry.FormalDeformation.CompleteLocal.PowerSeries

/-!
# Minimal versal formal objects

A predeformation category with a versal formal object admits a minimal versal
formal object, unique up to isomorphism; every versal object is the pushforward
of a minimal versal formal object along a finite-variable power series extension.
-/

@[expose] public section

open CategoryTheory
open CompleteLocalAlgCat

universe u

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable {F : Type (u + 1)} [Category.{u + 1} F]
variable {p : F ⥤ ArtinianLocalAlgCat Λ k}

namespace FormalObject

/-- A predeformation category with a versal formal object has a minimal versal
formal object. -/
theorem exists_isMinimalVersal [Functor.IsPredeformationCategory p]
    (ξ : FormalObject p) [IsVersal ξ] :
    ∃ ξ' : FormalObject p, IsMinimalVersal ξ' :=
  sorry

/-- Any two minimal versal formal objects of a predeformation category are isomorphic. -/
theorem nonempty_iso [Functor.IsPredeformationCategory p]
    (ξ η : FormalObject p) [IsMinimalVersal ξ] [IsMinimalVersal η] :
    Nonempty (ξ ≅ η) :=
  sorry

/-- Every versal formal object of a predeformation category receives a morphism from
a minimal versal formal object whose base map is a finite-variable power series extension. -/
theorem exists_isPowerSeriesOver [Functor.IsPredeformationCategory p]
    (ξ : FormalObject p) [IsVersal ξ] :
    ∃ (ξ' : FormalObject p) (f : ξ' ⟶ ξ),
      IsMinimalVersal ξ' ∧ IsPowerSeriesOver f.base :=
  sorry

/-- Every morphism between minimal versal formal objects of a predeformation category
is an isomorphism. -/
instance isIso [Functor.IsPredeformationCategory p]
    {ξ η : FormalObject p} [IsMinimalVersal ξ] [IsMinimalVersal η]
    (f : ξ ⟶ η) : IsIso f :=
  sorry

/-- A versal formal object of a predeformation category whose differential is
bijective on residue-derivation orbits is minimal versal. -/
theorem isMinimalVersal_of_bijectiveDifferentialOnOrbits
    [Functor.IsPredeformationCategory p] (ξ : FormalObject p) [IsVersal ξ]
    (h : BijectiveDifferentialOnOrbits ξ) : IsMinimalVersal ξ := sorry

/-- A versal formal object with Fact-certified orbit bijectivity of its
differential is minimal versal. -/
instance instIsMinimalVersalOfBijectiveDifferentialOnOrbits
    [Functor.IsPredeformationCategory p] (ξ : FormalObject p) [IsVersal ξ]
    [Fact (BijectiveDifferentialOnOrbits ξ)] : IsMinimalVersal ξ :=
  isMinimalVersal_of_bijectiveDifferentialOnOrbits ξ Fact.out

/-- Any two versal formal objects of a predeformation category whose differentials
are bijective on residue-derivation orbits are isomorphic. -/
theorem nonempty_iso_of_bijectiveDifferentialOnOrbits
    [Functor.IsPredeformationCategory p] (ξ η : FormalObject p)
    [IsVersal ξ] [IsVersal η] (hξ : BijectiveDifferentialOnOrbits ξ)
    (hη : BijectiveDifferentialOnOrbits η) : Nonempty (ξ ≅ η) := sorry

/-- The differential of a minimal versal formal object of a predeformation category
satisfying Schlessinger's condition (S2) is bijective on residue-derivation orbits. -/
theorem bijectiveDifferentialOnOrbits_of_isMinimalVersal
    [Functor.IsPredeformationCategory p] [Functor.HasSchlessingerS2 p]
    (ξ : FormalObject p) [IsMinimalVersal ξ] :
    BijectiveDifferentialOnOrbits ξ := sorry

end FormalObject
