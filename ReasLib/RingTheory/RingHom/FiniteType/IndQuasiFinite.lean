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
public import Mathlib.RingTheory.RingHomProperties
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.RingHom.FiniteType.QuasiFinite
public import ReasLib.RingTheory.RingHom.IndQuasiFinite

/-!
# Finite-type ind-quasi-finite ring maps

Mathlib's `RingHom.IndQuasiFinite` is built from its finite-fibre predicate.
This module defines the stronger filtered-colimit condition in which every
stage is also of finite type, together with its bridge to the underlying
ind-quasi-finite predicate.
-/

@[expose] public section

open CategoryTheory MorphismProperty

universe u v w

namespace CommRingCat

/-- The morphism property consisting of finite-type quasi-finite ring maps. -/
abbrev finiteTypeQuasiFinite : MorphismProperty CommRingCat.{u} :=
  RingHom.toMorphismProperty RingHom.FiniteType.QuasiFinite

/-- Finite-type quasi-finite morphisms of commutative rings are invariant
under isomorphisms. -/
instance finiteTypeQuasiFinite_respectsIso :
    CommRingCat.finiteTypeQuasiFinite.RespectsIso := sorry

end CommRingCat

namespace RingHom.FiniteType

section

variable {R : Type u} {A : Type v} [CommRing R] [CommRing A]

/-- The representation-level finite-type ind-quasi-finite predicate with an
arbitrary universe for its filtered presentation. -/
abbrev IndQuasiFinite.Raw (f : R →+* A) : Prop :=
  ind.{w, max u v, max u v + 1} CommRingCat.finiteTypeQuasiFinite
    (CommRingCat.ofHom f.ulift.{v, u})

/-- A ring map is finite-type ind-quasi-finite when it is a filtered colimit
of finite-type quasi-finite ring maps.  The public owner fixes the endpoint
universe; arbitrary presentation sizes belong to
`RingHom.FiniteType.IndQuasiFinite.Raw`. -/
abbrev IndQuasiFinite (f : R →+* A) : Prop :=
  IndQuasiFinite.Raw.{u, v, max u v} f

end

namespace IndQuasiFinite

section

variable {R : Type u} {A : Type v} [CommRing R] [CommRing A]

/-- An arbitrary-size finite-type ind-quasi-finite presentation induces the
canonical endpoint-universe predicate. -/
theorem ofRaw (f : R →+* A) (h : RingHom.FiniteType.IndQuasiFinite.Raw.{u, v, w} f) :
    RingHom.FiniteType.IndQuasiFinite f := sorry

/-- A finite-type quasi-finite ring map is finite-type ind-quasi-finite. -/
theorem ofQuasiFinite (f : R →+* A) (hf : RingHom.FiniteType.QuasiFinite f) :
    RingHom.FiniteType.IndQuasiFinite f := sorry

/-- Forgetting the finite-type condition on every stage gives Mathlib's core
ind-quasi-finite predicate. -/
theorem toIndQuasiFinite (f : R →+* A) (h : RingHom.FiniteType.IndQuasiFinite f) :
    RingHom.IndQuasiFinite f := sorry

end

end IndQuasiFinite

namespace IndQuasiFinite.Raw

section

variable {R : Type u} {A : Type v} [CommRing R] [CommRing A]

/-- A finite-type quasi-finite ring map has an arbitrary-size finite-type
ind-quasi-finite presentation. -/
theorem ofQuasiFinite (f : R →+* A) (hf : RingHom.FiniteType.QuasiFinite f) :
    RingHom.FiniteType.IndQuasiFinite.Raw f := sorry

end

end IndQuasiFinite.Raw

namespace IndQuasiFinite.Raw

section

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]

/-- The unlifted categorical finite-type ind-quasi-finite condition on an
algebra map is equivalent to the representation-level ring-map predicate. -/
theorem algebraMap_iff :
    ind.{v, u, u + 1} CommRingCat.finiteTypeQuasiFinite
        (CommRingCat.ofHom (algebraMap R A)) ↔
      RingHom.FiniteType.IndQuasiFinite.Raw.{u, u, v} (algebraMap R A) := sorry

/-- An unlifted categorical finite-type ind-quasi-finite presentation of an
algebra map induces the arbitrary-size ring-map presentation. -/
theorem of_ind
    (h : ind.{v, u, u + 1} CommRingCat.finiteTypeQuasiFinite
      (CommRingCat.ofHom (algebraMap R A))) :
    RingHom.FiniteType.IndQuasiFinite.Raw.{u, u, v} (algebraMap R A) := sorry

end

end IndQuasiFinite.Raw

end RingHom.FiniteType
