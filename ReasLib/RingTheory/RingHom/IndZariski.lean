module

public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.Algebra.Ring.ULift
public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.CategoryTheory.MorphismProperty.Ind
public import Mathlib.RingTheory.LocalIso
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Ind-Zariski ring homomorphisms

An ind-Zariski commutative-ring homomorphism is a filtered colimit of local
isomorphisms in the sense of `Algebra.IsLocalIso`. The public predicate applies
to arbitrary ring maps, with arbitrary presentation universes available through
`RingHom.IndZariski.Raw`.
-/

open CategoryTheory Limits MorphismProperty RingHom CommRingCat.Hom

universe u v w

namespace CommRingCat

/-- The morphism property on `CommRingCat` consisting of local isomorphisms. -/
abbrev localIso : MorphismProperty CommRingCat.{u} :=
  fun _ _ f => @Algebra.IsLocalIso _ _ _ _ f.hom.toAlgebra

/-- A morphism of commutative rings is a local isomorphism precisely when the
induced algebra structure satisfies `Algebra.IsLocalIso`. -/
theorem localIso_iff {R S : CommRingCat.{u}} (f : R ⟶ S) :
    localIso f ↔ @Algebra.IsLocalIso R S _ _ f.hom.toAlgebra := sorry

/-- Local isomorphisms of commutative rings are invariant under isomorphisms. -/
instance localIso_respectsIso : CommRingCat.localIso.RespectsIso := sorry

end CommRingCat

namespace RingHom

section

variable {R : Type u} {A : Type v} [CommRing R] [CommRing A]

/-- A ring map has an ind-Zariski presentation in the specified universe when
it is a filtered colimit of local isomorphisms. -/
abbrev IndZariski.Raw (f : R →+* A) : Prop :=
  ind.{w, max u v, max u v + 1} CommRingCat.localIso
    (CommRingCat.ofHom f.ulift.{v, u})

/-- A ring map is ind-Zariski when it is a filtered colimit of local
isomorphisms in the canonical endpoint universe. -/
abbrev IndZariski (f : R →+* A) : Prop :=
  IndZariski.Raw.{u, v, max u v} f

end

namespace IndZariski

section

variable {R : Type u} {A : Type v} [CommRing R] [CommRing A]

/-- An arbitrary-size categorical presentation induces the canonical
ind-Zariski predicate. -/
theorem ofRaw (f : R →+* A) (h : IndZariski.Raw.{u, v, w} f) :
    f.IndZariski := sorry

end

section

variable {R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A]

/-- A local isomorphism is ind-Zariski. -/
theorem ofIsLocalIso [Algebra.IsLocalIso R A] :
    (algebraMap R A).IndZariski := sorry

end

end IndZariski

namespace IndZariski.Raw

section

variable {R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A]

/-- A local isomorphism has an arbitrary-size ind-Zariski presentation. -/
theorem ofIsLocalIso [Algebra.IsLocalIso R A] :
    RingHom.IndZariski.Raw (algebraMap R A) := sorry

end

end IndZariski.Raw

namespace IndZariski.Raw

section

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]

/-- The unlifted categorical ind-Zariski condition on an algebra map is
equivalent to `RingHom.IndZariski.Raw`. -/
theorem algebraMap_iff :
    ind.{v, u, u + 1} CommRingCat.localIso (CommRingCat.ofHom (algebraMap R A)) ↔
      RingHom.IndZariski.Raw.{u, u, v} (algebraMap R A) := sorry

/-- An unlifted categorical ind-Zariski presentation of an algebra map induces
the arbitrary-size ring-map presentation. -/
theorem of_ind
    (h : ind.{v, u, u + 1} CommRingCat.localIso
      (CommRingCat.ofHom (algebraMap R A))) :
    RingHom.IndZariski.Raw.{u, u, v} (algebraMap R A) := sorry

end

section

variable {R : Type u} [CommRing R]
variable {J : Type v} [Category.{v} J] [IsFiltered J]

/-- A filtered colimit in the under-category of a commutative ring preserves
the ind-Zariski condition on its structure maps. -/
theorem of_isColimit
    (F : J ⥤ Under (CommRingCat.of R)) (c : Cocone F) (hc : IsColimit c)
    (hF : ∀ j, ind.{v, u, u + 1} CommRingCat.localIso (F.obj j).hom) :
    ind.{v, u, u + 1} CommRingCat.localIso c.pt.hom := sorry

end

section

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
variable {J : Type v} [Category.{v} J] [IsFiltered J]

/-- The filtered-colimit condition on an algebra map is obtained from a
colimit vertex identified with the target algebra. -/
theorem algebraMap_of_isColimit
    (F : J ⥤ Under (CommRingCat.of R)) (c : Cocone F) (hc : IsColimit c)
    (e : c.pt ≅ Under.mk (CommRingCat.ofHom (algebraMap R A)))
    (hF : ∀ j, ind.{v, u, u + 1} CommRingCat.localIso (F.obj j).hom) :
    RingHom.IndZariski.Raw.{u, u, v} (algebraMap R A) := sorry

end

end IndZariski.Raw

namespace IndZariski

section

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
variable {J : Type v} [Category.{v} J] [IsFiltered J]

/-- A filtered colimit of ind-Zariski algebras over a fixed commutative ring
is ind-Zariski over that ring. -/
@[stacks 096S "filtered colimits of ind-Zariski maps"]
theorem of_isColimit
    (F : J ⥤ Under (CommRingCat.of R)) (c : Cocone F) (hc : IsColimit c)
    (e : c.pt ≅ Under.mk (CommRingCat.ofHom (algebraMap R A)))
    (hF : ∀ j, (hom (F.obj j).hom).IndZariski) :
    (algebraMap R A).IndZariski := sorry

end

end IndZariski

end RingHom
