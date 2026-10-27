/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.UniversallyInjective
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.RelativeConditions
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Pullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Surjective
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Radicial

/-!
# Weakly radicial morphisms of algebraic spaces

A morphism of algebraic spaces is weakly radicial when every field-valued fibre
has singleton points space and admits a monomorphism from the spectrum of a
purely inseparable extension of the source field. Among surjective morphisms,
this weakens the requirement that the reduced fibre be isomorphic to such a
spectrum. Radicial morphisms in general may also have empty fibres.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- An algebraic space over `Spec(K)` has singleton points space and admits a
monomorphism from `Spec(L)` over `Spec(K)` for a purely inseparable field
extension `L / K`. -/
def isWeaklyRadicialOver {S : Scheme.{u}} {K : Type u} [Field K]
    (σ : Spec (.of K) ⟶ S) {X : AlgebraicSpace S}
    (π : X ⟶ ofOver (Over.mk σ)) : Prop :=
  Nonempty (Points X) ∧ Subsingleton (Points X) ∧
    ∃ (L : Type u) (_ : Field L) (_ : Algebra K L) (_ : IsPurelyInseparable K L)
      (ι : specFieldExtension σ L ⟶ X),
      Mono ι ∧ ι ≫ π = specFieldExtensionHom σ L

/-- Unfolding of `isWeaklyRadicialOver`. -/
theorem isWeaklyRadicialOver_iff {S : Scheme.{u}} {K : Type u} [Field K]
    (σ : Spec (.of K) ⟶ S) {X : AlgebraicSpace S}
    (π : X ⟶ ofOver (Over.mk σ)) :
    isWeaklyRadicialOver σ π ↔
      Nonempty (Points X) ∧ Subsingleton (Points X) ∧
        ∃ (L : Type u) (_ : Field L) (_ : Algebra K L) (_ : IsPurelyInseparable K L)
          (ι : specFieldExtension σ L ⟶ X),
          Mono ι ∧ ι ≫ π = specFieldExtensionHom σ L :=
  Iff.rfl

namespace isWeaklyRadicialOver

/-- An algebraic space over `Spec(K)` with singleton points and a monomorphism
from `Spec(L)` over `Spec(K)` for a purely inseparable extension `L / K`
satisfies `isWeaklyRadicialOver`. -/
theorem of {S : Scheme.{u}} {K : Type u} [Field K] (σ : Spec (.of K) ⟶ S)
    {X : AlgebraicSpace S} (π : X ⟶ ofOver (Over.mk σ))
    (h_points : Nonempty (Points X) ∧ Subsingleton (Points X)) (L : Type u)
    [Field L] [Algebra K L] [IsPurelyInseparable K L]
    (ι : specFieldExtension σ L ⟶ X) [Mono ι]
    (h_triangle : ι ≫ π = specFieldExtensionHom σ L) :
    isWeaklyRadicialOver σ π :=
  ⟨h_points.1, h_points.2, L, inferInstance, inferInstance, inferInstance, ι,
    inferInstance, h_triangle⟩

/-- `isWeaklyRadicialOver` implies singleton points and a monomorphism from
`Spec(L)` over `Spec(K)` for a purely inseparable extension `L / K`. -/
theorem spec {S : Scheme.{u}} {K : Type u} [Field K] (σ : Spec (.of K) ⟶ S)
    {X : AlgebraicSpace S} (π : X ⟶ ofOver (Over.mk σ))
    (h : isWeaklyRadicialOver σ π) :
    Nonempty (Points X) ∧ Subsingleton (Points X) ∧
      ∃ (L : Type u) (_ : Field L) (_ : Algebra K L) (_ : IsPurelyInseparable K L)
        (ι : specFieldExtension σ L ⟶ X),
        Mono ι ∧ ι ≫ π = specFieldExtensionHom σ L :=
  h

/-- A weakly radicial fibre over `Spec(K)` has singleton points space. -/
theorem unique_points {S : Scheme.{u}} {K : Type u} [Field K]
    (σ : Spec (.of K) ⟶ S) {X : AlgebraicSpace S}
    (π : X ⟶ ofOver (Over.mk σ)) (h : isWeaklyRadicialOver σ π) :
    Nonempty (Points X) ∧ Subsingleton (Points X) :=
  ⟨h.1, h.2.1⟩

/-- A weakly radicial fibre over `Spec(K)` admits a monomorphism from `Spec(L)`
over `Spec(K)` for a purely inseparable extension `L / K`. -/
theorem exists_mono {S : Scheme.{u}} {K : Type u} [Field K]
    (σ : Spec (.of K) ⟶ S) {X : AlgebraicSpace S}
    (π : X ⟶ ofOver (Over.mk σ)) (h : isWeaklyRadicialOver σ π) :
    ∃ (L : Type u) (_ : Field L) (_ : Algebra K L) (_ : IsPurelyInseparable K L)
      (ι : specFieldExtension σ L ⟶ X),
      Mono ι ∧ ι ≫ π = specFieldExtensionHom σ L :=
  h.2.2

end isWeaklyRadicialOver

/-- A morphism of algebraic spaces is weakly radicial if every field-valued fibre
has singleton points space and admits a monomorphism from the spectrum of a
purely inseparable extension of the source field. -/
@[mk_iff]
class WeaklyRadicial {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    Prop where
  /-- Every fibre `Spec(K) ×_Y X` is weakly radicial over `Spec(K)`. -/
  fieldValuedPullback :
    ∀ p : FieldValuedPoint Y,
      isWeaklyRadicialOver p.structureHom (pullback.fst p.hom f)

private theorem weaklyRadicial_points_mk_eq_of_factorization
    {S : Scheme.{u}} {X : AlgebraicSpace S} {p q : FieldValuedPoint X}
    (φ : FieldValuedPoint.Factorization p q) : Points.mk p = Points.mk q := by
  apply Quotient.sound
  refine ⟨⟨p, ⟨𝟙 _, Category.id_comp _, ?_⟩, φ⟩⟩
  change yoneda.map (𝟙 p.overObj) ≫ p.hom = p.hom
  rw [yoneda.map_id, Category.id_comp]

private theorem weaklyRadicial_points_of_split_mono
    {S : Scheme.{u}} {K : Type u} [Field K] (σ : Spec (.of K) ⟶ S)
    {X : AlgebraicSpace S} (π : X ⟶ ofOver (Over.mk σ)) [Mono π]
    (s : ofOver (Over.mk σ) ⟶ X) (hs : s ≫ π = 𝟙 _) :
    Nonempty (Points X) ∧ Subsingleton (Points X) := by
  let p : FieldValuedPoint X := FieldValuedPoint.of K σ s
  have hq (q : FieldValuedPoint X) : Points.mk q = Points.mk p := by
    let a : q.overObj ⟶ Over.mk σ := yoneda.preimage (q.hom ≫ π)
    have ha : ofOverHomMk (σK := q.structureHom) (σL := σ) a.left (Over.w a) =
        q.hom ≫ π := yoneda.map_preimage _
    have hqs : (q.hom ≫ π) ≫ s = q.hom := by
      apply (cancel_mono π).1
      rw [Category.assoc, hs, Category.comp_id]
    apply weaklyRadicial_points_mk_eq_of_factorization
    refine FieldValuedPoint.Factorization.of a.left (Over.w a) ?_
    exact (congrArg (fun t : ofOver (Over.mk q.structureHom) ⟶ ofOver (Over.mk σ) ↦
      t ≫ s) ha).trans hqs
  refine ⟨⟨Points.mk p⟩, ⟨?_⟩⟩
  intro x y
  refine Quotient.inductionOn₂ x y ?_
  intro q r
  exact (hq q).trans (hq r).symm

namespace WeaklyRadicial

/-- The identity morphism of an algebraic space is weakly radicial. -/
instance id {S : Scheme.{u}} {X : AlgebraicSpace S} : WeaklyRadicial (𝟙 X) := by
  letI : Mono (𝟙 X) := ⟨fun _ _ h ↦ by simpa only [Category.comp_id] using h⟩
  constructor
  intro p
  letI : Mono (𝟙 (ofOver (Over.mk p.structureHom))) :=
    ⟨fun _ _ h ↦ by simpa only [Category.comp_id] using h⟩
  let s : ofOver (Over.mk p.structureHom) ⟶ pullback p.hom (𝟙 X) :=
    pullback.lift (𝟙 _) p.hom (by simp)
  have hs : s ≫ pullback.fst p.hom (𝟙 X) = 𝟙 _ := pullback.lift_fst _ _ _
  haveI : Mono s := mono_of_mono_fac hs
  have hK : Spec.map (CommRingCat.ofHom (algebraMap p.K p.K)) = 𝟙 _ :=
    Spec.map_id _
  let a : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap p.K p.K)) ≫ p.structureHom) ⟶
      Over.mk p.structureHom :=
    Over.homMk (Spec.map (CommRingCat.ofHom (algebraMap p.K p.K))) rfl
  haveI : Mono a.left := by
    change Mono (Spec.map (CommRingCat.ofHom (algebraMap p.K p.K)))
    rw [hK]
    infer_instance
  haveI : Mono a := Over.mono_of_mono_left a
  haveI : Mono (specFieldExtensionHom p.structureHom p.K) := by
    constructor
    intro Z g h hgh
    exact (cancel_mono (yoneda.map a)).1 hgh
  refine isWeaklyRadicialOver.of _ _
    (weaklyRadicial_points_of_split_mono p.structureHom _ s hs) p.K
    (specFieldExtensionHom p.structureHom p.K ≫ s) ?_
  rw [Category.assoc, hs, Category.comp_id]

/-- A weakly radicial morphism has weakly radicial field-valued fibres. -/
theorem spec {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    [WeaklyRadicial f] (p : FieldValuedPoint Y) :
    isWeaklyRadicialOver p.structureHom (pullback.fst p.hom f) :=
  WeaklyRadicial.fieldValuedPullback p

/-- A morphism is weakly radicial as soon as every field-valued fibre is weakly
radicial over `Spec(K)`. -/
theorem of {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    (hf : ∀ p : FieldValuedPoint Y,
      isWeaklyRadicialOver p.structureHom (pullback.fst p.hom f)) :
    WeaklyRadicial f :=
  ⟨hf⟩

/-- A weakly radicial morphism has singleton field-valued fibres. -/
theorem unique_points {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    [WeaklyRadicial f] (p : FieldValuedPoint Y) :
    Nonempty (Points (pullback p.hom f)) ∧
      Subsingleton (Points (pullback p.hom f)) :=
  isWeaklyRadicialOver.unique_points _ _ (spec p)

/-- A weakly radicial morphism has, on every field-valued fibre, a monomorphism
from `Spec(L)` over `Spec(K)` for a purely inseparable extension `L / K`. -/
theorem exists_mono {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    [WeaklyRadicial f] (p : FieldValuedPoint Y) :
    ∃ (L : Type u) (_ : Field L) (_ : Algebra p.K L)
      (_ : IsPurelyInseparable p.K L)
      (ι : specFieldExtension p.structureHom L ⟶ pullback p.hom f),
      Mono ι ∧
        ι ≫ pullback.fst p.hom f = specFieldExtensionHom p.structureHom L :=
  isWeaklyRadicialOver.exists_mono _ _ (spec p)

/-- A weakly radicial morphism is surjective, since every field-valued fibre has
singleton points space. -/
instance surjective {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [WeaklyRadicial f] : Surjective f := by
  constructor
  intro y
  refine Quotient.inductionOn y ?_
  intro p
  obtain ⟨L, hL, hA, hpi, ι, _, hι⟩ := exists_mono (f := f) p
  letI := hL
  letI := hA
  letI := hpi
  let q : FieldValuedPoint X := FieldValuedPoint.of L
    (Spec.map (CommRingCat.ofHom (algebraMap p.K L)) ≫ p.structureHom)
    (ι ≫ pullback.snd p.hom f)
  refine ⟨Points.mk q, ?_⟩
  change Points.mk (q.map f) = Points.mk p
  apply weaklyRadicial_points_mk_eq_of_factorization
  refine FieldValuedPoint.Factorization.of
    (Spec.map (CommRingCat.ofHom (algebraMap p.K L))) rfl ?_
  change specFieldExtensionHom p.structureHom L ≫ p.hom =
    (ι ≫ pullback.snd p.hom f) ≫ f
  rw [Category.assoc, ← pullback.condition, ← Category.assoc, hι]

end WeaklyRadicial

/-- A morphism of algebraic spaces is weakly radicial if and only if for every
field `K` and every morphism `Spec(K) ⟶ Y`, the fibre `Spec(K) ×_Y X` is weakly
radicial over `Spec(K)`. -/
theorem weaklyRadicial_iff_forall_specField {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    WeaklyRadicial f ↔
      ∀ (K : Type u) [Field K] (σ : Spec (.of K) ⟶ S)
        (g : ofOver (Over.mk σ) ⟶ Y),
        isWeaklyRadicialOver σ (pullback.fst g f) := by
  constructor
  · intro hf K _ σ g
    exact hf.fieldValuedPullback (FieldValuedPoint.of K σ g)
  · intro hf
    exact ⟨fun p ↦ hf p.K p.structureHom p.hom⟩

/-- A nonempty field-valued fibre of a universally injective morphism with
property (β) has singleton points and contains a purely inseparable field spectrum
as a monomorphism over the source field. -/
@[stacks 049E]
theorem isWeaklyRadicialOver.of_universallyInjective_of_propertyBeta
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [UniversallyInjective f] [PropertyBeta f] (p : FieldValuedPoint Y)
    (hne : Nonempty (Points (pullback p.hom f))) :
    isWeaklyRadicialOver p.structureHom (pullback.fst p.hom f) :=
  sorry

namespace WeaklyRadicial

/-- A surjective weakly radicial morphism is surjective on points valued in
any algebraically closed field. -/
@[stacks 049E]
theorem surjectiveOnAlgClosedFieldPoints {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    {f : X ⟶ Y} [WeaklyRadicial f] [Surjective f] (k : Type u) [Field k]
    [IsAlgClosed k] (σ : Spec (.of k) ⟶ S) :
    Function.Surjective (fun x : ofOver (Over.mk σ) ⟶ X ↦ x ≫ f) := by
  intro y
  obtain ⟨L, hL, hA, hpi, ι, _, hι⟩ :=
    isWeaklyRadicialOver.exists_mono σ (pullback.fst y f)
      ((weaklyRadicial_iff_forall_specField f).mp inferInstance k σ y)
  letI : Field L := hL
  letI : Algebra k L := hA
  letI : IsPurelyInseparable k L := hpi
  let φ : L →ₐ[k] k := IsAlgClosed.lift
  have hφ : CommRingCat.ofHom (algebraMap k L) ≫ CommRingCat.ofHom φ.toRingHom =
      𝟙 (CommRingCat.of k) := by
    ext x
    exact φ.commutes x
  have hSpec : Spec.map (CommRingCat.ofHom φ.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap k L)) = 𝟙 _ := by
    rw [← Spec.map_comp, hφ, Spec.map_id]
  let a : Over.mk σ ⟶
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k L)) ≫ σ) :=
    Over.homMk (Spec.map (CommRingCat.ofHom φ.toRingHom)) (by
      change Spec.map (CommRingCat.ofHom φ.toRingHom) ≫
        (Spec.map (CommRingCat.ofHom (algebraMap k L)) ≫ σ) = σ
      rw [← Category.assoc, hSpec, Category.id_comp])
  let b : ofOver (Over.mk σ) ⟶ specFieldExtension σ L := yoneda.map a
  have hb : b ≫ specFieldExtensionHom σ L = 𝟙 _ := by
    change yoneda.map a ≫ yoneda.map _ = 𝟙 _
    rw [← yoneda.map_comp, ← yoneda.map_id (Over.mk σ)]
    congr 1
    exact Over.OverMorphism.ext hSpec
  refine ⟨b ≫ ι ≫ pullback.snd y f, ?_⟩
  calc
    (b ≫ ι ≫ pullback.snd y f) ≫ f =
        b ≫ ι ≫ pullback.fst y f ≫ y := by
          simp only [Category.assoc, ← pullback.condition]
    _ = y := by rw [← Category.assoc ι, hι, ← Category.assoc, hb, Category.id_comp]

/-- A surjective universally injective morphism with property (β) is weakly radicial. -/
@[stacks 049E]
instance of_universallyInjective_of_propertyBeta {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [UniversallyInjective f]
    [PropertyBeta f] [Surjective f] : WeaklyRadicial f := by
  constructor
  intro p
  apply isWeaklyRadicialOver.of_universallyInjective_of_propertyBeta f p
  obtain ⟨x, hx⟩ := Surjective.map_surjective (f := f) (Points.mk p)
  revert hx
  refine Quotient.inductionOn x ?_
  intro q hq
  have heq : Points.mk (q.map f) = Points.mk p := hq
  obtain ⟨e⟩ := Quotient.exact heq
  let a := ofOverHomMk e.right.schemeHom e.right.fac_structure
  let b := ofOverHomMk e.left.schemeHom e.left.fac_structure ≫ q.hom
  have hab : a ≫ p.hom = b ≫ f :=
    e.right.fac_hom.trans e.left.fac_hom.symm
  exact ⟨Points.mk (FieldValuedPoint.of e.point.K e.point.structureHom
    (pullback.lift a b hab))⟩

end WeaklyRadicial

end AlgebraicGeometry.AlgebraicSpace
