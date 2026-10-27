/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

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
    localIso f ↔ @Algebra.IsLocalIso R S _ _ f.hom.toAlgebra := Iff.rfl

/-- Local isomorphisms of commutative rings are invariant under isomorphisms. -/
instance localIso_respectsIso : CommRingCat.localIso.RespectsIso := by
  refine RespectsIso.mk _ ?_ ?_
  · intro R S T e f hf
    letI := e.hom.hom.toAlgebra
    letI := f.hom.toAlgebra
    letI := (f.hom.comp e.hom.hom).toAlgebra
    haveI : IsScalarTower R S T := .of_algebraMap_eq' rfl
    haveI : Algebra.IsStandardOpenImmersion R S :=
      .of_bijective e.commRingCatIsoToRingEquiv.bijective
    haveI : Algebra.IsLocalIso S T := hf
    exact Algebra.IsLocalIso.trans R S T
  · intro R S T e f hf
    letI := f.hom.toAlgebra
    letI := e.hom.hom.toAlgebra
    letI := (e.hom.hom.comp f.hom).toAlgebra
    haveI : IsScalarTower R S T := .of_algebraMap_eq' rfl
    haveI : Algebra.IsStandardOpenImmersion S T :=
      .of_bijective e.commRingCatIsoToRingEquiv.bijective
    haveI : Algebra.IsLocalIso R S := hf
    exact Algebra.IsLocalIso.trans R S T

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

private theorem isLocalIso_ulift [Algebra.IsLocalIso R A] :
    @Algebra.IsLocalIso (ULift.{v} R) (ULift.{u} A) _ _
      ((algebraMap R A).ulift.{v, u}).toAlgebra := by
  letI : Algebra (ULift.{v} R) R := ULift.ringEquiv.toRingHom.toAlgebra
  letI : Algebra A (ULift.{u} A) := ULift.ringEquiv.symm.toRingHom.toAlgebra
  letI : Algebra (ULift.{v} R) A :=
    ((algebraMap R A).comp ULift.ringEquiv.toRingHom).toAlgebra
  letI : Algebra (ULift.{v} R) (ULift.{u} A) :=
    ((algebraMap R A).ulift.{v, u}).toAlgebra
  haveI := IsScalarTower.of_algebraMap_eq'
    (R := ULift.{v} R) (S := R) (A := A) (by rfl)
  haveI := IsScalarTower.of_algebraMap_eq'
    (R := ULift.{v} R) (S := A) (A := ULift.{u} A) (by rfl)
  haveI : Algebra.IsStandardOpenImmersion (ULift.{v} R) R :=
    .of_bijective ULift.ringEquiv.bijective
  haveI : Algebra.IsStandardOpenImmersion A (ULift.{u} A) :=
    .of_bijective ULift.ringEquiv.symm.bijective
  haveI : Algebra.IsLocalIso (ULift.{v} R) A :=
    .trans (ULift.{v} R) R A
  exact Algebra.IsLocalIso.trans (ULift.{v} R) A (ULift.{u} A)

/-- A local isomorphism is ind-Zariski. -/
theorem ofIsLocalIso [Algebra.IsLocalIso R A] :
    (algebraMap R A).IndZariski :=
  le_ind CommRingCat.localIso _ (isLocalIso_ulift (R := R) (A := A))

end

end IndZariski

namespace IndZariski.Raw

section

variable {R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A]

/-- A local isomorphism has an arbitrary-size ind-Zariski presentation. -/
theorem ofIsLocalIso [Algebra.IsLocalIso R A] :
    RingHom.IndZariski.Raw (algebraMap R A) :=
  le_ind CommRingCat.localIso _ (IndZariski.isLocalIso_ulift (R := R) (A := A))

end

end IndZariski.Raw

namespace IndZariski.Raw

section

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]

/-- The unlifted categorical ind-Zariski condition on an algebra map is
equivalent to `RingHom.IndZariski.Raw`. -/
theorem algebraMap_iff :
    ind.{v, u, u + 1} CommRingCat.localIso (CommRingCat.ofHom (algebraMap R A)) ↔
      RingHom.IndZariski.Raw.{u, u, v} (algebraMap R A) := by
  apply (ind.{v} CommRingCat.localIso).arrow_mk_iso_iff
  exact Arrow.isoMk
    (ULift.ringEquiv : ULift.{u} R ≃+* R).symm.toCommRingCatIso
    (ULift.ringEquiv : ULift.{u} A ≃+* A).symm.toCommRingCatIso
    (by rfl)

/-- An unlifted categorical ind-Zariski presentation of an algebra map induces
the arbitrary-size ring-map presentation. -/
theorem of_ind
    (h : ind.{v, u, u + 1} CommRingCat.localIso
      (CommRingCat.ofHom (algebraMap R A))) :
    RingHom.IndZariski.Raw.{u, u, v} (algebraMap R A) :=
  algebraMap_iff.mp h

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
    RingHom.IndZariski.Raw.{u, u, v} (algebraMap R A) :=
  of_ind (((ind.{v} CommRingCat.localIso).under_iso_iff e).mp
    (of_isColimit F c hc hF))

end

end IndZariski.Raw

namespace IndZariski

private theorem ind_universeLift {R A : CommRingCat.{u}} (f : R ⟶ A)
    (h : ind.{v} CommRingCat.localIso f) :
    ind.{max v w} CommRingCat.localIso f := by
  rw [ind_iff_ind_underMk] at h ⊢
  obtain ⟨J, _, _, pres, hpres⟩ := h
  exact ObjectProperty.of_essentiallySmall_index pres hpres

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
    (algebraMap R A).IndZariski := by
  let d : AsSmall.{u} J ≌ J := AsSmall.equiv.symm
  haveI : IsFiltered (AsSmall.{u} J) := .of_equivalence d.symm
  apply ofRaw.{u, u, max u v} (algebraMap R A)
  apply Raw.algebraMap_of_isColimit (d.functor ⋙ F) (c.whisker d.functor)
    (hc.whiskerEquivalence d) e
  intro j
  letI := (F.obj (d.functor.obj j)).hom.hom.toAlgebra
  exact ind_universeLift _ (Raw.algebraMap_iff.mpr (hF (d.functor.obj j)))

end

end IndZariski

end RingHom
