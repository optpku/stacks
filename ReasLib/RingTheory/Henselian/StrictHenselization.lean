/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import Mathlib.RingTheory.Noetherian.Basic
public import ReasLib.RingTheory.Henselian.StrictHenselian
public import ReasLib.RingTheory.RingHom.IndEtale.Basic

@[expose] public section

/-!
# Strict Henselizations of Local Rings

This module owns the reusable proposition that a local algebra is a strict henselization of its
base, together with its intrinsic existence theorem. It deliberately records only the intrinsic
map property; chosen separable closures and comparison maps are construction-specific data.
-/

open IsLocalRing

universe u v

section

variable (R : Type u) [CommRing R] [IsLocalRing R]
variable (S : Type v) [CommRing S] [Algebra R S]

/-- A local `R`-algebra `S` is a strict henselization of `R` when its structural map is local and
ind-etale, its target is strictly henselian, and it identifies maximal ideals. -/
@[stacks 04GP "strict henselization owner"]
class IsStrictHenselizationOf : Prop extends StrictHenselianLocalRing S,
  IsLocalHom (algebraMap R S) where
  isFilteredColimitOfEtale : RingHom.IndEtale (algebraMap R S)
  map_maximalIdeal :
    Ideal.map (algebraMap R S) (maximalIdeal R) = maximalIdeal S

namespace IsStrictHenselizationOf

variable {R : Type u} [CommRing R] [IsLocalRing R]
variable {S : Type v} [CommRing S] [Algebra R S] [IsStrictHenselizationOf R S]

/-- A strict henselization of a Noetherian local ring is Noetherian. This is a named theorem,
rather than an instance, because the target ring does not determine its base ring. -/
@[stacks 06LJ "Noetherianity of a strict henselization"]
theorem isNoetherianRing [IsNoetherianRing R] : IsNoetherianRing S := sorry

/-- The structural map of a strict henselization is local. -/
@[stacks 04GP "locality of a strict henselization map"]
instance isLocalHom : IsLocalHom (algebraMap R S) :=
  IsStrictHenselizationOf.toIsLocalHom

/-- The structural map of a strict henselization is ind-etale. -/
@[stacks 04GP "ind-etaleness of a strict henselization map"]
theorem indEtale : RingHom.IndEtale (algebraMap R S) :=
  IsStrictHenselizationOf.isFilteredColimitOfEtale

/-- The structural map of a strict henselization has a representation-level
ind-etale presentation in the canonical endpoint universe. -/
@[stacks 04GP "raw ind-etale presentation of a strict henselization map"]
theorem rawIndEtale : RingHom.IndEtale.Raw.{u, v, max u v} (algebraMap R S) :=
  indEtale

/-- The defining strictly-henselian, local, ind-etale, and closed-point conditions of a strict
henselization. -/
@[stacks 04GP "strict henselization specification"]
theorem spec :
    StrictHenselianLocalRing S ∧
      IsLocalHom (algebraMap R S) ∧
        RingHom.IndEtale (algebraMap R S) ∧
          Ideal.map (algebraMap R S) (maximalIdeal R) = maximalIdeal S := sorry

/-- Every local ring admits a strict henselization. The statement does not
specify a chosen separable closure of the residue field or compatibility with
such a choice. -/
@[stacks 04GP "existence of strict henselizations"]
theorem exists_strict (R : Type u) [CommRing R] [IsLocalRing R] :
    ∃ (S : Type u) (_ : CommRing S) (_ : Algebra R S), IsStrictHenselizationOf R S := sorry

end IsStrictHenselizationOf

end
