module

public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.Algebra.Ring.ULift
public import Mathlib.CategoryTheory.MorphismProperty.Ind
public import Mathlib.RingTheory.RingHom.Etale
public import Mathlib.RingTheory.RingHomProperties
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Ind-etale ring homomorphisms

This module owns the categorical presentation of an ind-etale commutative-ring
homomorphism.  The public predicate is phrased for an arbitrary ring map; the
`ULift` bookkeeping required by the categorical owner remains implementation
detail.
-/

open CategoryTheory MorphismProperty RingHom

universe u v w

namespace CommRingCat

/-- The morphism property on `CommRingCat` consisting of etale ring maps. -/
abbrev etale : MorphismProperty CommRingCat.{u} :=
  fun _ _ f => f.hom.Etale

/-- Etale morphisms of commutative rings are invariant under isomorphisms. -/
instance etale_respectsIso : CommRingCat.etale.RespectsIso := sorry

end CommRingCat

namespace RingHom

section

variable {R : Type u} {A : Type v} [CommRing R] [CommRing A]

/-- The representation-level ind-etale predicate with an arbitrary universe
for the filtered presentation. -/
abbrev IndEtale.Raw (f : R →+* A) : Prop :=
  ind.{w, max u v, max u v + 1} CommRingCat.etale
    (CommRingCat.ofHom f.ulift.{v, u})

/-- A ring map is ind-etale when it is a filtered colimit of etale algebras.
The public owner uses the canonical endpoint universe; arbitrary presentation
sizes belong to `IndEtale.Raw`. -/
@[stacks 097I "ind-etale ring maps"]
abbrev IndEtale (f : R →+* A) : Prop :=
  IndEtale.Raw.{u, v, max u v} f

end

namespace IndEtale

section

variable {R : Type u} {A : Type v} [CommRing R] [CommRing A]

/-- An arbitrary-size categorical presentation induces the canonical
ind-etale predicate. -/
theorem ofRaw (f : R →+* A) (h : IndEtale.Raw.{u, v, w} f) :
    f.IndEtale := sorry

/-- An etale ring map is ind-etale. -/
theorem ofEtale (f : R →+* A) (hf : f.Etale) : f.IndEtale := sorry

/-- A bijective ring map is ind-etale. -/
theorem ofBijective (f : R →+* A) (hf : Function.Bijective f) :
    f.IndEtale := sorry

end


end IndEtale

namespace IndEtale.Raw

section

variable {R : Type u} {A : Type v} [CommRing R] [CommRing A]

/-- An etale ring map has an arbitrary-size ind-etale presentation. -/
theorem ofEtale (f : R →+* A) (hf : f.Etale) : RingHom.IndEtale.Raw f := sorry

/-- A bijective ring map has an arbitrary-size ind-etale presentation. -/
theorem ofBijective (f : R →+* A) (hf : Function.Bijective f) :
    RingHom.IndEtale.Raw f := sorry

end

end IndEtale.Raw

namespace IndEtale.Raw

section

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]

/-- The unlifted categorical ind-etale condition on an algebra map is
equivalent to `RingHom.IndEtale.Raw`; this removes representation-specific
`ULift` bookkeeping from downstream statements. -/
theorem algebraMap_iff :
    ind.{v, u, u + 1} CommRingCat.etale (CommRingCat.ofHom (algebraMap R A)) ↔
      RingHom.IndEtale.Raw.{u, u, v} (algebraMap R A) := sorry

/-- An unlifted categorical ind-etale presentation of an algebra map induces
the arbitrary-size ring-map presentation. -/
theorem of_ind
    (h : ind.{v, u, u + 1} CommRingCat.etale (CommRingCat.ofHom (algebraMap R A))) :
    RingHom.IndEtale.Raw.{u, u, v} (algebraMap R A) := sorry

end

end IndEtale.Raw

end RingHom
