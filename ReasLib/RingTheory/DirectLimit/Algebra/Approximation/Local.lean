/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.DirectLimit.Algebra.Approximation
public import ReasLib.RingTheory.DirectLimit.Algebra.Approximation.Limit
public import Mathlib.RingTheory.LocalRing.RingHom.Basic
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Locality properties of directed ring-hom approximations

This leaf records the local-ring and local-homomorphism hypotheses attached to
an approximation independently of its finiteness properties.  The stage data
remain owned by `Hom`; this property bundle can therefore be combined with
other approximation hypotheses without introducing a second data owner.
-/

@[expose] public section

universe u v w

namespace Ring.DirectLimit.Algebra.Approximation

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]

namespace Hom

variable {f : R →+* S}

/-- Locality conditions for a directed ring-hom approximation.

The bundle keeps all conditions as propositions over the canonical stage
objects of `A`.  It is deliberately separate from `FiniteType`, so a caller
can assume locality without importing or constructing finiteness data. -/
@[stacks 00R1 "directed approximation locality"]
class Local (A : Hom f) : Prop where
  /-- Every source stage is a local ring. -/
  source (i : A.index) : IsLocalRing (A.source i)
  /-- Every source transition is a local homomorphism. -/
  sourceMap {i j : A.index} (h : i ≤ j) :
    IsLocalHom (A.sourceMap i j h)
  /-- Every target stage is a local ring. -/
  target (i : A.index) : IsLocalRing (A.target i)
  /-- Every stage map is a local homomorphism. -/
  map (i : A.index) : IsLocalHom (A.map i)
  /-- Every target transition is a local homomorphism. -/
  targetMap {i j : A.index} (h : i ≤ j) :
    IsLocalHom (A.targetMap i j h)

attribute [instance] Local.source Local.sourceMap Local.target Local.map Local.targetMap

namespace Local

/-- The defining locality conditions, grouped into stage, transition, and
stage-map bundles for source-facing arguments. -/
@[stacks 00R1 "directed approximation locality"]
theorem spec (A : Hom f) [A.Local] :
    (∀ i : A.index,
        IsLocalRing (A.source i) ∧ IsLocalRing (A.target i)) ∧
      (∀ {i j : A.index} (h : i ≤ j),
        IsLocalHom (A.sourceMap i j h) ∧
          IsLocalHom (A.targetMap i j h)) ∧
      (∀ i : A.index, IsLocalHom (A.map i)) := sorry

/-- The chosen source colimit equivalence transports the canonical local-ring
structure on the source direct limit to the limiting source ring. -/
@[stacks 00R1 "directed approximation locality"]
theorem sourceColimit (A : Hom f) [A.Local] : IsLocalRing R := sorry

/-- The chosen target colimit equivalence transports the canonical local-ring
structure on the target direct limit to the limiting target ring. -/
@[stacks 00R1 "directed approximation locality"]
theorem targetColimit (A : Hom f) [A.Local] : IsLocalRing S := sorry

/-- The canonical source-stage map to the limiting source ring is local. -/
@[stacks 00R1 "directed approximation locality"]
theorem sourceToLimit (A : Hom f) [A.Local] (i : A.index) :
    IsLocalHom (A.sourceToLimit i) := sorry

/-- The canonical target-stage map to the limiting target ring is local. -/
@[stacks 00R1 "directed approximation locality"]
theorem targetToLimit (A : Hom f) [A.Local] (i : A.index) :
    IsLocalHom (A.targetToLimit i) := sorry

/-- The stage map into the limiting target, obtained by composing the stage
map with the canonical target-stage map, is local. -/
@[stacks 00R1 "directed approximation locality"]
theorem mapToLimit (A : Hom f) [A.Local] (i : A.index) :
    IsLocalHom (A.mapToLimit i) := sorry

/-- The limiting ring homomorphism represented by a local directed
approximation is local. -/
@[stacks 00R1 "directed approximation locality"]
theorem limitMap (A : Hom f) [A.Local] : IsLocalHom f := sorry

/- The stage-to-limit maps are canonical local homomorphisms determined by the
approximation and stage, so typeclass search may use them directly.  The
colimit and limiting-map results above are intentionally left as explicit
theorems because their conclusions do not retain the approximation parameter. -/
attribute [instance] Local.sourceToLimit Local.targetToLimit Local.mapToLimit

end Local

end Hom

end Ring.DirectLimit.Algebra.Approximation
