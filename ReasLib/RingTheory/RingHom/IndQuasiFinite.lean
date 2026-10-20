/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.Algebra.Ring.ULift
public import Mathlib.CategoryTheory.MorphismProperty.Ind
public import Mathlib.RingTheory.RingHom.QuasiFinite
public import Mathlib.RingTheory.RingHomProperties
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Ind-quasi-finite ring maps

This module owns the categorical presentation of a commutative-ring map that
is a filtered colimit of quasi-finite maps.  The public predicate is stated
directly for a ring homomorphism; the universe lift required by the
categorical presentation is confined to `RingHom.IndQuasiFinite.Raw`.
-/

@[expose] public section

open CategoryTheory MorphismProperty

universe u v w

namespace CommRingCat

/-- The morphism property on `CommRingCat` consisting of quasi-finite ring
maps. -/
abbrev quasiFinite : MorphismProperty CommRingCat.{u} :=
  RingHom.toMorphismProperty RingHom.QuasiFinite

/-- Quasi-finite morphisms of commutative rings are invariant under
isomorphisms. -/
instance quasiFinite_respectsIso : CommRingCat.quasiFinite.RespectsIso := sorry

end CommRingCat

namespace RingHom

section

variable {R : Type u} {A : Type v} [CommRing R] [CommRing A]

/-- The representation-level ind-quasi-finite predicate with an arbitrary
universe for its filtered presentation. -/
abbrev IndQuasiFinite.Raw (f : R →+* A) : Prop :=
  ind.{w, max u v, max u v + 1} CommRingCat.quasiFinite
    (CommRingCat.ofHom f.ulift.{v, u})

/-- A ring map is ind-quasi-finite when it is a filtered colimit of
quasi-finite ring maps.  The public owner fixes the endpoint universe;
arbitrary presentation sizes belong to `RingHom.IndQuasiFinite.Raw`. -/
abbrev IndQuasiFinite (f : R →+* A) : Prop :=
  IndQuasiFinite.Raw.{u, v, max u v} f

end

namespace IndQuasiFinite

section

variable {R : Type u} {A : Type v} [CommRing R] [CommRing A]

/-- An arbitrary-size filtered presentation by quasi-finite maps induces the
canonical ind-quasi-finite predicate. -/
theorem ofRaw (f : R →+* A) (h : IndQuasiFinite.Raw.{u, v, w} f) :
    f.IndQuasiFinite := sorry

/-- A quasi-finite ring map is ind-quasi-finite. -/
theorem ofQuasiFinite (f : R →+* A) (hf : f.QuasiFinite) :
    f.IndQuasiFinite := sorry

end

end IndQuasiFinite

namespace IndQuasiFinite.Raw

section

variable {R : Type u} {A : Type v} [CommRing R] [CommRing A]

/-- A quasi-finite ring map has an arbitrary-size ind-quasi-finite
presentation. -/
theorem ofQuasiFinite (f : R →+* A) (hf : f.QuasiFinite) :
    RingHom.IndQuasiFinite.Raw f := sorry

end

end IndQuasiFinite.Raw

namespace IndQuasiFinite.Raw

section

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]

/-- The unlifted categorical ind-quasi-finite condition on an algebra map is
equivalent to `RingHom.IndQuasiFinite.Raw`.  This keeps universe-lift
bookkeeping out of downstream statements. -/
theorem algebraMap_iff :
    ind.{v, u, u + 1} CommRingCat.quasiFinite
        (CommRingCat.ofHom (algebraMap R A)) ↔
      RingHom.IndQuasiFinite.Raw.{u, u, v} (algebraMap R A) := sorry

/-- An unlifted categorical ind-quasi-finite presentation of an algebra map
induces the reusable ring-map predicate. -/
theorem of_ind
    (h : ind.{v, u, u + 1} CommRingCat.quasiFinite
      (CommRingCat.ofHom (algebraMap R A))) :
    RingHom.IndQuasiFinite.Raw.{u, u, v} (algebraMap R A) := sorry

end

end IndQuasiFinite.Raw

end RingHom
