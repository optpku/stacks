/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.CommAlgCat.Basic
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Maps to a fixed commutative algebra

This leaf owns the map, kernel, and contraction data carried by an object of
`CategoryTheory.Over (CommAlgCat.of R T)`.  It deliberately does not assume
that the source object is etale, or that the target is a field.  More
specialized owners may build localization or residue-field constructions from
this interface.

@stack 04GV
-/

open CategoryTheory

universe u v

namespace CommAlgCat.Over.Target

variable {R : Type u} {T : Type v} [CommRing R] [CommRing T] [Algebra R T]

/-- The structural map from an object over the fixed target. -/
@[stacks 04GV "structural map of an over-object"]
abbrev map (A : CategoryTheory.Over (CommAlgCat.of R T)) : A.left →+* T :=
  A.hom.hom.toRingHom

/-- The underlying ring map of a morphism over the fixed target. -/
@[stacks 04GV "underlying map of an over-object morphism"]
abbrev hom {A B : CategoryTheory.Over (CommAlgCat.of R T)} (f : A ⟶ B) :
    A.left →+* B.left :=
  f.left.hom.toRingHom

/-- The kernel of the structural map to the fixed target. -/
@[stacks 04GV "kernel of an over-object target map"]
noncomputable abbrev kernel (A : CategoryTheory.Over (CommAlgCat.of R T)) : Ideal A.left :=
  RingHom.ker (map A)

/-- A morphism over the target preserves structural maps to that target. -/
@[stacks 04GV "target-map naturality for over-object morphisms"]
theorem map_comp {A B : CategoryTheory.Over (CommAlgCat.of R T)} (f : A ⟶ B) :
    (map B).comp (hom f) = map A := sorry

/-- The kernel selected by the target map contracts along an over-object morphism. -/
@[stacks 04GV "kernel contraction for over-object morphisms"]
theorem kernel_comap {A B : CategoryTheory.Over (CommAlgCat.of R T)} (f : A ⟶ B) :
    kernel A = Ideal.comap (hom f) (kernel B) := sorry

/-- The kernel of a structural map to a domain is prime. -/
@[stacks 04GV "primality of an over-object target kernel"]
instance kernel_isPrime [IsDomain T] (A : CategoryTheory.Over (CommAlgCat.of R T)) :
    (kernel A).IsPrime := sorry

/-- The structural target map restricts to the fixed algebra map on the base ring. -/
@[stacks 04GV "base compatibility of an over-object target map"]
theorem map_comp_algebraMap (A : CategoryTheory.Over (CommAlgCat.of R T)) :
    (map A).comp (algebraMap R A.left) = algebraMap R T := sorry

/-- The target kernel contracts to the kernel of the fixed base-to-target map. -/
@[stacks 04GV "base-kernel contraction for an over-object target"]
theorem kernel_comap_algebraMap (A : CategoryTheory.Over (CommAlgCat.of R T)) :
    RingHom.ker (algebraMap R T) =
      Ideal.comap (algebraMap R A.left) (kernel A) := sorry

/-- An explicit base kernel identifies the corresponding contraction to the target kernel. -/
@[stacks 04GV "base-prime contraction for an over-object target"]
theorem baseComap {p : Ideal R} [p.IsPrime]
    (hbase : RingHom.ker (algebraMap R T) = p)
    (A : CategoryTheory.Over (CommAlgCat.of R T)) :
    p = Ideal.comap (algebraMap R A.left) (kernel A) := sorry

end CommAlgCat.Over.Target
