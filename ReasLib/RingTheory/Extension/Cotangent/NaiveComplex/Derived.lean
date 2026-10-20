/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Extension.Cotangent.NaiveComplex.Canonical
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat
public import Mathlib.Algebra.Homology.Embedding.Extend

/-!
# Derived naive cotangent objects

@stack 07BN

This file sends the canonical two-term naive cotangent complex to the standard derived category
of modules.  Presentation-level chain complexes remain owned by
`Algebra.Extension.NaiveCotangent`; this leaf only owns their canonical derived views.
-/

@[expose] public section

open CategoryTheory ComplexShape
open scoped NaiveCotangent

noncomputable section

universe u v

namespace Algebra

variable (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]

/-- The object of `DerivedCategory (ModuleCat S)` represented by the canonical naive cotangent
complex of the algebra map `R → S`. -/
@[stacks 07BN "derived view of the canonical naive cotangent complex"]
abbrev naiveCotangentObject : DerivedCategory (ModuleCat S) :=
  DerivedCategory.Q.obj ((NL{S⁄R}).extend embeddingDownNat)

end Algebra

namespace CommRingCat.Hom

variable {R S : CommRingCat.{u}}

/-- The derived naive cotangent object attached to a bundled commutative-ring morphism. -/
@[stacks 07BN "derived bundled ring morphism view"]
abbrev naiveCotangentObject (f : R ⟶ S) : DerivedCategory (ModuleCat S) :=
  DerivedCategory.Q.obj ((NL(f)).extend embeddingDownNat)

end CommRingCat.Hom

namespace RingHom

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]

/-- The derived naive cotangent object attached directly to a commutative-ring homomorphism. -/
@[stacks 07BN "derived ring-homomorphism view"]
abbrev naiveCotangentObject (f : R →+* S) : DerivedCategory (ModuleCat S) :=
  @Algebra.naiveCotangentObject R S _ _ f.toAlgebra

end RingHom
