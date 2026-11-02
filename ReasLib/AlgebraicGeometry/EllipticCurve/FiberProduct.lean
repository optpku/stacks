/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.EllipticCurve.Family
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting
public import Mathlib.CategoryTheory.Yoneda

/-!
# The fibre-product functor of elliptic curves

This file owns the functor `Schemeᵒᵖ ⥤ Type` sending a test scheme `T` to triples
`(a, a', α)` consisting of morphisms `a : T ⟶ S`, `a' : T ⟶ S'` and an isomorphism
of elliptic curves over `T` from `a* E` to `a'* E'`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.EllipticCurve

variable {S S' : Scheme.{u}} (E : Over S) (zero : S ⟶ E.left)
  (E' : Over S') (zero' : S' ⟶ E'.left)
  [IsEllipticCurve E zero] [IsEllipticCurve E' zero']

/-- A `T`-point of the fibre-product functor: morphisms `a : T ⟶ S` and `a' : T ⟶ S'`
together with an isomorphism of elliptic curves over `T` from `a* E` to `a'* E'`. -/
structure Triple (T : Scheme.{u}) : Type u where
  /-- The morphism from the test scheme to the base of `E`. -/
  a : T ⟶ S
  /-- The morphism from the test scheme to the base of `E'`. -/
  a' : T ⟶ S'
  /-- An isomorphism of elliptic curves over `T` from `a* E` to `a'* E'`. -/
  iso : HomOver (𝟙 T)
    (Over.mk (pullback.snd E.hom a)) (pullbackSection E zero a IsEllipticCurve.isSection)
    (Over.mk (pullback.snd E'.hom a')) (pullbackSection E' zero' a' IsEllipticCurve.isSection)

namespace Triple

variable {E zero E' zero'}

/-- A triple consists of a pair of base morphisms and a cartesian isomorphism of the
corresponding pullbacks that preserves zero sections. -/
theorem spec {T : Scheme.{u}} (p : Triple E zero E' zero' T) :
    IsPullback p.iso.hom (pullback.snd E.hom p.a) (pullback.snd E'.hom p.a') (𝟙 T) ∧
      pullbackSection E zero p.a IsEllipticCurve.isSection ≫ p.iso.hom =
        𝟙 T ≫ pullbackSection E' zero' p.a' IsEllipticCurve.isSection :=
  ⟨p.iso.isPullback, p.iso.comm_zero⟩

/-- The underlying isomorphism of total spaces obtained by pulling a triple back along
`g : T' ⟶ T`, via the canonical pasting identifications of iterated pullbacks. -/
def pullbackHom {T T' : Scheme.{u}} (p : Triple E zero E' zero' T) (g : T' ⟶ T) :
    pullback E.hom (g ≫ p.a) ⟶ pullback E'.hom (g ≫ p.a') :=
  (pullbackLeftPullbackSndIso E.hom p.a g).inv ≫
    pullback.map (pullback.snd E.hom p.a) g (pullback.snd E'.hom p.a') g
      p.iso.hom (𝟙 T') (𝟙 T) p.iso.isPullback.w.symm
      ((Category.comp_id g).trans (Category.id_comp g).symm) ≫
    (pullbackLeftPullbackSndIso E'.hom p.a' g).hom

set_option backward.isDefEq.respectTransparency false in
/-- The pulled-back isomorphism is cartesian over `𝟙 T'`. -/
theorem pullback_isPullback {T T' : Scheme.{u}} (p : Triple E zero E' zero' T)
    (g : T' ⟶ T) :
    IsPullback (p.pullbackHom g) (pullback.snd E.hom (g ≫ p.a))
      (pullback.snd E'.hom (g ≫ p.a')) (𝟙 T') := by
  haveI : IsIso p.iso.hom := p.iso.isPullback.isIso_fst_of_isIso
  unfold pullbackHom
  apply IsPullback.of_horiz_isIso
  exact ⟨by simp [pullback.map, Category.assoc]⟩

set_option backward.isDefEq.respectTransparency false in
/-- The pulled-back isomorphism preserves the lifted zero sections. -/
theorem pullback_comm_zero {T T' : Scheme.{u}} (p : Triple E zero E' zero' T)
    (g : T' ⟶ T) :
    pullbackSection E zero (g ≫ p.a) IsEllipticCurve.isSection ≫ p.pullbackHom g =
      𝟙 T' ≫ pullbackSection E' zero' (g ≫ p.a') IsEllipticCurve.isSection := by
  have hzero :
      pullbackSection E zero (g ≫ p.a) IsEllipticCurve.isSection ≫
          (pullbackLeftPullbackSndIso E.hom p.a g).inv ≫ pullback.fst _ _ =
        g ≫ pullbackSection E zero p.a IsEllipticCurve.isSection := by
    apply pullback.hom_ext
    · simp [Category.assoc, pullbackSection]
    · simp [Category.assoc, pullbackSection]
      exact Category.id_comp g
  apply pullback.hom_ext
  · calc
      _ = (pullbackSection E zero (g ≫ p.a) IsEllipticCurve.isSection ≫
          (pullbackLeftPullbackSndIso E.hom p.a g).inv ≫ pullback.fst _ _) ≫
            p.iso.hom ≫ pullback.fst _ _ := by
              simp [pullbackHom, pullback.map, Category.assoc]
      _ = (g ≫ pullbackSection E zero p.a IsEllipticCurve.isSection) ≫
          p.iso.hom ≫ pullback.fst _ _ := by rw [hzero]
      _ = _ := by
        simp only [← Category.assoc]
        rw [Category.assoc g _ p.iso.hom, p.iso.comm_zero]
        simp [Category.assoc, pullbackSection]
  · simp [pullbackHom, pullback.map, Category.assoc, pullbackSection]

/-- Restrict a triple along a morphism of test schemes. -/
def pullback {T T' : Scheme.{u}} (p : Triple E zero E' zero' T) (g : T' ⟶ T) :
    Triple E zero E' zero' T' where
  a := g ≫ p.a
  a' := g ≫ p.a'
  iso :=
    { hom := p.pullbackHom g
      isPullback := p.pullback_isPullback g
      comm_zero := p.pullback_comm_zero g }

set_option backward.isDefEq.respectTransparency false in
/-- Equality of the base maps and of the underlying total-space maps determines a triple. -/
private theorem ext_hom {T : Scheme.{u}} {p q : Triple E zero E' zero' T}
    (ha : p.a = q.a) (ha' : p.a' = q.a') (hh : HEq p.iso.hom q.iso.hom) : p = q := by
  cases p with
  | mk a a' φ =>
    cases q with
    | mk b b' ψ =>
      dsimp only at ha ha' hh
      subst b
      subst b'
      cases φ with
      | mk f hf hzero =>
        cases ψ with
        | mk g hg hzero' =>
          have h : f = g := eq_of_heq hh
          cases h
          rfl

end Triple

set_option backward.isDefEq.respectTransparency false in
/-- Identity morphisms act as the identity on triples. -/
theorem functor_map_id (T : Scheme.{u}ᵒᵖ) :
    TypeCat.ofHom (fun p : Triple E zero E' zero' T.unop ↦ p.pullback (𝟙 T).unop) =
      𝟙 (Triple E zero E' zero' T.unop) := by
  apply ConcreteCategory.hom_ext
  intro p
  change p.pullback (𝟙 T.unop) = p
  apply Triple.ext_hom
  · exact Category.id_comp p.a
  · exact Category.id_comp p.a'
  · dsimp only [Triple.pullback, Triple.pullbackHom]
    simp only [heq_eq_eq]
    have hid : (pullbackLeftPullbackSndIso E.hom p.a (𝟙 T.unop)).inv ≫
        pullback.fst _ _ = 𝟙 _ := by
      apply pullback.hom_ext <;> simp [Category.assoc] <;> rfl
    apply pullback.hom_ext
    · simp [pullback.map, Category.assoc, reassoc_of% hid]
      rfl
    · simp [pullback.map, Category.assoc]
      convert p.iso.isPullback.w.symm using 1 <;> rfl

set_option backward.isDefEq.respectTransparency false in
/-- Restriction of triples is compatible with composition of test morphisms. -/
theorem functor_map_comp {T T' T'' : Scheme.{u}ᵒᵖ} (h : T ⟶ T') (k : T' ⟶ T'') :
    TypeCat.ofHom (fun p : Triple E zero E' zero' T.unop ↦ p.pullback (h ≫ k).unop) =
      TypeCat.ofHom (fun p : Triple E zero E' zero' T.unop ↦ p.pullback h.unop) ≫
        TypeCat.ofHom (fun p : Triple E zero E' zero' T'.unop ↦ p.pullback k.unop) := by
  apply ConcreteCategory.hom_ext
  intro p
  change p.pullback (k.unop ≫ h.unop) = (p.pullback h.unop).pullback k.unop
  apply Triple.ext_hom
  · exact Category.assoc _ _ _
  · exact Category.assoc _ _ _
  · dsimp only [Triple.pullback, Triple.pullbackHom]
    simp only [heq_eq_eq]
    have hcomp :
        (pullbackLeftPullbackSndIso E.hom p.a (k.unop ≫ h.unop)).inv ≫ pullback.fst _ _ =
          (pullbackLeftPullbackSndIso E.hom (h.unop ≫ p.a) k.unop).inv ≫
            pullback.fst _ _ ≫ (pullbackLeftPullbackSndIso E.hom p.a h.unop).inv ≫
              pullback.fst _ _ := by
      apply pullback.hom_ext <;> simp [Category.assoc] <;> rfl
    have hfst' : pullback.fst E'.hom ((k.unop ≫ h.unop) ≫ p.a') =
        pullback.fst E'.hom (k.unop ≫ h.unop ≫ p.a') := rfl
    have hsnd' : pullback.snd E'.hom ((k.unop ≫ h.unop) ≫ p.a') =
        pullback.snd E'.hom (k.unop ≫ h.unop ≫ p.a') := rfl
    apply pullback.hom_ext
    · simp [pullback.map, Category.assoc, reassoc_of% hcomp]
      rw [hfst']
      simp [Category.assoc]
    · simp [pullback.map, Category.assoc]
      rw [hsnd']
      simp
      rfl

/-- The functor `Schemeᵒᵖ ⥤ Type` sending `T` to pairs of base morphisms
    `a : T.unop ⟶ S` and `a' : T.unop ⟶ S'` together with a section-preserving
    cartesian isomorphism between the pullbacks of `E` and `E'` along them. -/
def functor : Scheme.{u}ᵒᵖ ⥤ Type u where
  obj T := Triple E zero E' zero' T.unop
  map h := TypeCat.ofHom (fun p : Triple E zero E' zero' _ ↦ p.pullback h.unop)
  map_id := functor_map_id E zero E' zero'
  map_comp := functor_map_comp E zero E' zero'

/-- Evaluating the functor at `T` gives the type of triples over `T`. -/
theorem functor_obj (T : Scheme.{u}) :
    (functor E zero E' zero').obj (op T) = Triple E zero E' zero' T := rfl

/-- The functor acts on a morphism by restriction of triples. -/
theorem functor_map {T T' : Scheme.{u}ᵒᵖ} (h : T ⟶ T') :
    (functor E zero E' zero').map h =
      TypeCat.ofHom (fun p : Triple E zero E' zero' T.unop ↦ p.pullback h.unop) := rfl

/-- The presheaf of triples of base morphisms and section-preserving cartesian isomorphisms
    between the corresponding pullbacks is representable by a scheme. -/
@[instance]
theorem functor_isRepresentable :
    (functor E zero E' zero').IsRepresentable := sorry

end AlgebraicGeometry.EllipticCurve
