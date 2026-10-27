/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.CategoryTheory.MorphismProperty.Comma
public import Mathlib.CategoryTheory.MorphismProperty.Representable
public import Mathlib.CategoryTheory.Sites.SubcanonicalOver
public import Mathlib.CategoryTheory.Subobject.Basic
public import ReasLib.AlgebraicGeometry.Scheme.PreRelation.InvariantImmersion
public import ReasLib.AlgebraicGeometry.Scheme.PreRelation.Pullback.Hom
public import ReasLib.AlgebraicGeometry.Scheme.PreRelation.QuotientSheaf.Functoriality

/-!
# Locally closed subspaces of quotient sheaves

Pullback along the quotient atlas and quotienting the restricted relation give the
correspondence between locally closed subspaces and invariant locally closed subschemes.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme Limits MorphismProperty
open Functor.relativelyRepresentable

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.PreRelation

/-- A locally closed subspace of `U / R` is an fppf sheaf over `S` with a relative immersion
into the quotient sheaf, with respect to `uliftYoneda`. -/
structure LocallyClosedSubspace {S : Scheme.{u}} {U : Over S} (P : PreRelation U)
    [P.IsEtaleEquivalenceRelation] where
  /-- The fppf sheaf underlying the locally closed subspace. -/
  X : Sheaf (Scheme.fppfTopology.over S) (Type (u + 1))
  /-- The inclusion of the subspace into `U / R`. -/
  ι : X ⟶ P.quotientSheaf (Scheme.fppfTopology.over S)
  /-- The inclusion is a relative immersion with respect to `uliftYoneda`. -/
  isImmersion :
    (over (@AlgebraicGeometry.IsImmersion)).relative uliftYoneda.{u + 1} ι.hom

namespace LocallyClosedSubspace

variable {S : Scheme.{u}} {U : Over S} {P : PreRelation U} [P.IsEtaleEquivalenceRelation]

/-- The locally closed subspace determined by a relative immersion into the quotient sheaf. -/
def ofι {X : Sheaf (Scheme.fppfTopology.over S) (Type (u + 1))}
    (ι : X ⟶ P.quotientSheaf (Scheme.fppfTopology.over S))
    (immersion : (over (@AlgebraicGeometry.IsImmersion)).relative uliftYoneda.{u + 1} ι.hom) :
    LocallyClosedSubspace P where
  X := X
  ι := ι
  isImmersion := immersion

/-- A relative immersion of fppf sheaves is a monomorphism of underlying presheaves. -/
instance mono_hom (Z : LocallyClosedSubspace P) : Mono Z.ι.hom := by
  suffices ∀ {T : Over S} {a b : uliftYoneda.{u + 1}.obj T ⟶ Z.X.obj},
      a ≫ Z.ι.hom = b ≫ Z.ι.hom → a = b from
    ⟨fun _ _ h ↦ hom_ext_uliftYoneda (fun _ _ ↦ this (by simp only [Category.assoc, h]))⟩
  intro T a b h
  have : AlgebraicGeometry.IsImmersion (Z.isImmersion.rep.snd (a ≫ Z.ι.hom)).left :=
    Z.isImmersion.property_snd (a ≫ Z.ι.hom)
  have : Mono (Z.isImmersion.rep.snd (a ≫ Z.ι.hom)) := Over.mono_of_mono_left _
  suffices Z.isImmersion.rep.lift (g := a ≫ Z.ι.hom) a (𝟙 T) (by simp) =
      Z.isImmersion.rep.lift b (𝟙 T) (by simp [← h]) by
    simpa using uliftYoneda.congr_map this =≫ Z.isImmersion.rep.fst (a ≫ Z.ι.hom)
  simp only [← cancel_mono (Z.isImmersion.rep.snd (a ≫ Z.ι.hom)), lift_snd]

/-- The inclusion of a locally closed subspace is a relative immersion and a monomorphism
of underlying presheaves. -/
theorem spec (Z : LocallyClosedSubspace P) :
    (over (@AlgebraicGeometry.IsImmersion)).relative uliftYoneda.{u + 1} Z.ι.hom ∧
      Mono Z.ι.hom :=
  ⟨Z.isImmersion, inferInstance⟩

/-- The subobject of the underlying quotient presheaf represented by a locally closed
subspace. -/
def subobject (Z : LocallyClosedSubspace P) :
    Subobject (P.quotientSheaf (Scheme.fppfTopology.over S)).obj :=
  Subobject.mk Z.ι.hom

/-- The subobject of a locally closed subspace is represented by its inclusion. -/
theorem subobject_eq_mk (Z : LocallyClosedSubspace P) :
    Z.subobject = @Subobject.mk _ _ _ _ Z.ι.hom (mono_hom Z) := rfl

/-- Two locally closed subspace presentations are equivalent when their subobjects agree. -/
def subobjectSetoid (P : PreRelation U) [P.IsEtaleEquivalenceRelation] :
    Setoid (LocallyClosedSubspace P) where
  r first second := first.subobject = second.subobject
  iseqv := ⟨fun _ => rfl, fun equality => equality.symm,
    fun first second => first.trans second⟩

/-- Locally closed subspaces of the quotient, independent of their sheaf presentations. -/
def SubobjectClass (P : PreRelation U) [P.IsEtaleEquivalenceRelation] :=
  Quotient (subobjectSetoid P)

private theorem subobject_eq_of_represented_pullbacks
    {V A B : Over S} {F G : (Over S)ᵒᵖ ⥤ Type (u + 1)}
    {f : F ⟶ G} {g : uliftYoneda.{u + 1}.obj V ⟶ G}
    {i : A ⟶ V} {j : B ⟶ V} [Mono i.left] [Mono j.left]
    {a : uliftYoneda.{u + 1}.obj A ⟶ F} {b : uliftYoneda.{u + 1}.obj B ⟶ F}
    (ha : IsPullback a (uliftYoneda.map i) f g)
    (hb : IsPullback b (uliftYoneda.map j) f g) :
    Subobject.mk i.left = Subobject.mk j.left := by
  let e : A ≅ B := uliftYoneda.{u + 1}.preimageIso (ha.isoIsPullback _ _ hb)
  apply Subobject.mk_eq_mk_of_comm i.left j.left ((Over.forget S).mapIso e)
  have w : e.hom ≫ j = i := by
    apply uliftYoneda.{u + 1}.map_injective
    simpa [e] using ha.isoIsPullback_hom_snd hb
  exact congrArg Over.Hom.left w

/-- The invariant immersion obtained by pulling a subspace back along the quotient atlas. -/
def pullbackAlong (Z : LocallyClosedSubspace P) : InvariantImmersion P where
  Z := Z.isImmersion.rep.pullback (P.quotientMap (Scheme.fppfTopology.over S)).hom
  ι := Z.isImmersion.rep.snd (P.quotientMap (Scheme.fppfTopology.over S)).hom
  isImmersion := Z.isImmersion.property_snd (P.quotientMap (Scheme.fppfTopology.over S)).hom
  isInvariant := by
    let q := (P.quotientMap (Scheme.fppfTopology.over S)).hom
    let i := Z.isImmersion.rep.snd q
    have : AlgebraicGeometry.IsImmersion i.left := Z.isImmersion.property_snd q
    have : Mono i := Over.mono_of_mono_left _
    change (Subobject.pullback P.t.left).obj (Subobject.mk i.left) =
      (Subobject.pullback P.s.left).obj (Subobject.mk i.left)
    have ht : IsPullback (Limits.pullback.fst i P.t).left
        (Limits.pullback.snd i P.t).left i.left P.t.left :=
      (IsPullback.of_hasPullback i P.t).map (Over.forget S)
    have hs : IsPullback (Limits.pullback.fst i P.s).left
        (Limits.pullback.snd i P.s).left i.left P.s.left :=
      (IsPullback.of_hasPullback i P.s).map (Over.forget S)
    refine (Subobject.pullback_obj_mk ht).trans
      (Eq.trans ?_ (Subobject.pullback_obj_mk hs).symm)
    refine subobject_eq_of_represented_pullbacks
      (b := uliftYoneda.map (Limits.pullback.fst i P.s) ≫ Z.isImmersion.rep.fst q)
      (((IsPullback.of_hasPullback i P.t).map uliftYoneda).paste_horiz
        (Z.isImmersion.rep.isPullback q)) ?_
    have hq : uliftYoneda.{u + 1}.map P.s ≫ q = uliftYoneda.map P.t ≫ q :=
      congrArg (fun k ↦ k.hom) (P.quotientMap_s_eq_t (Scheme.fppfTopology.over S))
    simpa only [hq] using
      (((IsPullback.of_hasPullback i P.s).map uliftYoneda).paste_horiz
        (Z.isImmersion.rep.isPullback q))

/-- The underlying scheme of the atlas pullback is the represented fibre product. -/
theorem pullbackAlong_Z (Z : LocallyClosedSubspace P) :
    (pullbackAlong Z).Z =
      Z.isImmersion.rep.pullback (P.quotientMap (Scheme.fppfTopology.over S)).hom := rfl

/-- The inclusion of the atlas pullback is the represented pullback projection. -/
theorem pullbackAlong_ι (Z : LocallyClosedSubspace P) :
    (pullbackAlong Z).ι =
      Z.isImmersion.rep.snd (P.quotientMap (Scheme.fppfTopology.over S)).hom := rfl

/-- Atlas pullback sends equal subspace subobjects to equal subscheme subobjects. -/
theorem pullbackAlong_respects_subobject {first second : LocallyClosedSubspace P}
    (equality : first.subobject = second.subobject) :
    first.pullbackAlong.subobject = second.pullbackAlong.subobject := by
  have hle (A B : LocallyClosedSubspace P) (h : A.subobject ≤ B.subobject) :
      A.pullbackAlong.subobject ≤ B.pullbackAlong.subobject := by
    let q := (P.quotientMap (Scheme.fppfTopology.over S)).hom
    let f := Subobject.ofMkLEMk A.ι.hom B.ι.hom h
    have w : (A.isImmersion.rep.fst q ≫ f) ≫ B.ι.hom =
        uliftYoneda.map (A.isImmersion.rep.snd q) ≫ q := by
      rw [Category.assoc, Subobject.ofMkLEMk_comp]
      exact A.isImmersion.rep.w q
    exact Subobject.mk_le_mk_of_comm
      (B.isImmersion.rep.lift (A.isImmersion.rep.fst q ≫ f)
        (A.isImmersion.rep.snd q) w).left
      (congrArg Over.Hom.left (B.isImmersion.rep.lift_snd _ _ w))
  exact le_antisymm (hle first second equality.le) (hle second first equality.ge)

end LocallyClosedSubspace

namespace InvariantImmersion

variable {S : Scheme.{u}} {U : Over S} {P : PreRelation U} [P.IsEtaleEquivalenceRelation]

/-- The subspace obtained by quotienting the restriction of the relation to an invariant
immersion. -/
def toLocallyClosedSubspace (Z' : InvariantImmersion P) : LocallyClosedSubspace P where
  X := (P.pullback Z'.ι).quotientSheaf (Scheme.fppfTopology.over S)
  ι := (P.pullbackHom Z'.ι).quotientSheafMap (Scheme.fppfTopology.over S)
  isImmersion := sorry

/-- The underlying sheaf of the descended subspace is the quotient of the restricted relation. -/
theorem toLocallyClosedSubspace_X (Z' : InvariantImmersion P) :
    (toLocallyClosedSubspace Z').X =
      (P.pullback Z'.ι).quotientSheaf (Scheme.fppfTopology.over S) := rfl

/-- The descended inclusion is the map on quotient sheaves induced by restriction. -/
theorem toLocallyClosedSubspace_ι (Z' : InvariantImmersion P) :
    (toLocallyClosedSubspace Z').ι =
      (P.pullbackHom Z'.ι).quotientSheafMap (Scheme.fppfTopology.over S) := rfl

/-- The quotient of an invariant immersion is relatively closed if and only if the original
immersion is closed. -/
theorem isClosedImmersion_toLocallyClosedSubspace_iff (Z' : InvariantImmersion P) :
    (over (@AlgebraicGeometry.IsClosedImmersion)).relative uliftYoneda.{u + 1}
        (toLocallyClosedSubspace Z').ι.hom ↔
      AlgebraicGeometry.IsClosedImmersion Z'.ι.left := sorry

/-- The quotient of an invariant immersion is relatively open if and only if the original
immersion is open. -/
theorem isOpenImmersion_toLocallyClosedSubspace_iff (Z' : InvariantImmersion P) :
    (over (@AlgebraicGeometry.IsOpenImmersion)).relative uliftYoneda.{u + 1}
        (toLocallyClosedSubspace Z').ι.hom ↔
      AlgebraicGeometry.IsOpenImmersion Z'.ι.left := sorry

/-- Quotienting the restricted relation sends equal subscheme subobjects to equal subspace
subobjects. -/
theorem toLocallyClosedSubspace_respects_subobject {first second : InvariantImmersion P}
    (equality : first.subobject = second.subobject) :
    first.toLocallyClosedSubspace.subobject = second.toLocallyClosedSubspace.subobject := by
  have hle (A B : InvariantImmersion P) (h : A.subobject ≤ B.subobject) :
      A.toLocallyClosedSubspace.subobject ≤ B.toLocallyClosedSubspace.subobject := by
    let f := Subobject.ofMkLEMk A.ι.left B.ι.left h
    have w : f ≫ B.ι.left = A.ι.left := Subobject.ofMkLEMk_comp h
    let g : A.Z ⟶ B.Z := Over.homMk f (by
      rw [← B.ι.w, ← Category.assoc, w]
      exact A.ι.w)
    have wg : g ≫ B.ι = A.ι := Over.OverMorphism.ext w
    let η : (P.pullback A.ι).quotientPresheaf ⟶
        (P.pullback B.ι).quotientPresheaf :=
      { app := fun T ↦ TypeCat.ofHom <| Quot.map (fun x ↦ x ≫ g) (by
          intro x y hxy
          apply (P.pullback_pointRel_iff B.ι T.unop (x ≫ g) (y ≫ g)).2
          simpa only [Category.assoc, wg] using
            (P.pullback_pointRel_iff A.ι T.unop x y).1 hxy)
        naturality := by
          intro T T' k
          ext x
          induction x using Quot.ind with
          | _ x =>
            change Quot.mk _ ((k.unop ≫ x) ≫ g) = Quot.mk _ (k.unop ≫ (x ≫ g))
            rw [Category.assoc] }
    have hη : η ≫ (P.pullbackHom B.ι).quotientPresheafMap =
        (P.pullbackHom A.ι).quotientPresheafMap := by
      ext T x
      induction x using Quot.ind with
      | _ x =>
        change Quot.mk _ ((x ≫ g) ≫ B.ι) = Quot.mk _ (x ≫ A.ι)
        rw [Category.assoc, wg]
    let φ := (presheafToSheaf (Scheme.fppfTopology.over S) (Type (u + 1))).map
      (Functor.whiskerRight η uliftFunctor.{u + 1, u})
    have : Mono A.toLocallyClosedSubspace.ι.hom := LocallyClosedSubspace.mono_hom _
    have : Mono B.toLocallyClosedSubspace.ι.hom := LocallyClosedSubspace.mono_hom _
    apply Subobject.mk_le_mk_of_comm
      (f₁ := A.toLocallyClosedSubspace.ι.hom)
      (f₂ := B.toLocallyClosedSubspace.ι.hom) φ.hom
    have hφ : φ ≫ (P.pullbackHom B.ι).quotientSheafMap (Scheme.fppfTopology.over S) =
        (P.pullbackHom A.ι).quotientSheafMap (Scheme.fppfTopology.over S) := by
      change (presheafToSheaf (Scheme.fppfTopology.over S) (Type (u + 1))).map
          (Functor.whiskerRight η uliftFunctor.{u + 1, u}) ≫
        (presheafToSheaf (Scheme.fppfTopology.over S) (Type (u + 1))).map
          (Functor.whiskerRight (P.pullbackHom B.ι).quotientPresheafMap
            uliftFunctor.{u + 1, u}) =
        (presheafToSheaf (Scheme.fppfTopology.over S) (Type (u + 1))).map
          (Functor.whiskerRight (P.pullbackHom A.ι).quotientPresheafMap
            uliftFunctor.{u + 1, u})
      rw [← Functor.map_comp, ← Functor.whiskerRight_comp, hη]
    exact congrArg (fun k ↦ k.hom) hφ
  exact le_antisymm (hle first second equality.le) (hle second first equality.ge)

end InvariantImmersion

/-- Pulling a subspace back along the quotient atlas and quotienting the restricted relation
recovers the original subspace subobject. -/
theorem pullbackAlong_toLocallyClosedSubspace_subobject {S : Scheme.{u}} {U : Over S}
    (P : PreRelation U) [P.IsEtaleEquivalenceRelation]
    (Z : LocallyClosedSubspace P) :
    (Z.pullbackAlong.toLocallyClosedSubspace).subobject = Z.subobject := sorry

/-- Quotienting an invariant immersion and pulling the descended subspace back along the
quotient atlas recovers the original subscheme subobject. -/
theorem toLocallyClosedSubspace_pullbackAlong_subobject {S : Scheme.{u}} {U : Over S}
    (P : PreRelation U) [P.IsEtaleEquivalenceRelation]
    (Z' : InvariantImmersion P) :
    (Z'.toLocallyClosedSubspace.pullbackAlong).subobject = Z'.subobject := sorry

/-- A subspace inclusion is relatively closed if and only if its atlas pullback is closed. -/
theorem isClosedImmersion_pullbackAlong_iff {S : Scheme.{u}} {U : Over S}
    (P : PreRelation U) [P.IsEtaleEquivalenceRelation]
    (Z : LocallyClosedSubspace P) :
    (over (@AlgebraicGeometry.IsClosedImmersion)).relative uliftYoneda.{u + 1} Z.ι.hom ↔
      AlgebraicGeometry.IsClosedImmersion Z.pullbackAlong.ι.left := by
  constructor
  · intro h
    exact h.property (P.quotientMap (Scheme.fppfTopology.over S)).hom _ _
      (Z.isImmersion.rep.isPullback _)
  · intro h
    sorry

/-- A subspace inclusion is relatively open if and only if its atlas pullback is open. -/
theorem isOpenImmersion_pullbackAlong_iff {S : Scheme.{u}} {U : Over S}
    (P : PreRelation U) [P.IsEtaleEquivalenceRelation]
    (Z : LocallyClosedSubspace P) :
    (over (@AlgebraicGeometry.IsOpenImmersion)).relative uliftYoneda.{u + 1} Z.ι.hom ↔
      AlgebraicGeometry.IsOpenImmersion Z.pullbackAlong.ι.left := by
  constructor
  · intro h
    exact h.property (P.quotientMap (Scheme.fppfTopology.over S)).hom _ _
      (Z.isImmersion.rep.isPullback _)
  · intro h
    sorry

/-- Invariant locally closed subschemes correspond to locally closed subspaces of the quotient
by descending the restricted relation, with inverse given by atlas pullback. -/
def locallyClosedSubspaceEquiv {S : Scheme.{u}} {U : Over S}
    (P : PreRelation U) [P.IsEtaleEquivalenceRelation] :
    InvariantImmersion.SubobjectClass P ≃ LocallyClosedSubspace.SubobjectClass P where
  toFun := Quotient.map InvariantImmersion.toLocallyClosedSubspace
    (fun {_ _} equality => InvariantImmersion.toLocallyClosedSubspace_respects_subobject equality)
  invFun := Quotient.map LocallyClosedSubspace.pullbackAlong
    (fun {_ _} equality => LocallyClosedSubspace.pullbackAlong_respects_subobject equality)
  left_inv := fun subscheme => Quotient.inductionOn subscheme fun representative =>
    Quotient.sound (toLocallyClosedSubspace_pullbackAlong_subobject P representative)
  right_inv := fun subspace => Quotient.inductionOn subspace fun representative =>
    Quotient.sound (pullbackAlong_toLocallyClosedSubspace_subobject P representative)

/-- The subspace correspondence sends an invariant immersion class to its restricted quotient
class. -/
theorem locallyClosedSubspaceEquiv_apply_mk {S : Scheme.{u}} {U : Over S}
    (P : PreRelation U) [P.IsEtaleEquivalenceRelation] (Z' : InvariantImmersion P) :
    locallyClosedSubspaceEquiv P (Quotient.mk (InvariantImmersion.subobjectSetoid P) Z') =
      Quotient.mk (LocallyClosedSubspace.subobjectSetoid P) Z'.toLocallyClosedSubspace := rfl

/-- The inverse subspace correspondence sends a subspace class to its atlas pullback class. -/
theorem locallyClosedSubspaceEquiv_symm_apply_mk {S : Scheme.{u}} {U : Over S}
    (P : PreRelation U) [P.IsEtaleEquivalenceRelation] (Z : LocallyClosedSubspace P) :
    (locallyClosedSubspaceEquiv P).symm (Quotient.mk (LocallyClosedSubspace.subobjectSetoid P) Z) =
      Quotient.mk (InvariantImmersion.subobjectSetoid P) Z.pullbackAlong := rfl

end AlgebraicGeometry.Scheme.PreRelation
