/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.FlatMono
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- A monomorphism of algebraic spaces over a scheme induces an injective map on points. -/
@[stacks 06RV]
theorem Points.map_injective_of_mono {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [Mono f] : Function.Injective (Points.map f) := sorry

namespace FieldValuedPoint

/-- A common extension gives a factorization through a monomorphic field-valued point. -/
theorem Factorization.nonempty_of_commonExtension_of_mono {S : Scheme.{u}}
    {X : AlgebraicSpace S} {p q : FieldValuedPoint X} (hq : Mono q.hom)
    (e : CommonExtension p q) : Nonempty (p.Factorization q) := by
  classical
  have hmono : Mono (C := (Over S)ᵒᵖ ⥤ Type u) q.hom := by
    refine ⟨fun {F} a b hab ↦ ?_⟩
    apply hom_ext_yoneda
    intro T t
    exact hq.right_cancellation (Z := ofOver T) (NatTrans.vcomp t a)
      (NatTrans.vcomp t b) (by
        change (t ≫ a) ≫ (q.hom : yoneda.obj q.overObj ⟶ X.functorOfPoints) =
          (t ≫ b) ≫ (q.hom : yoneda.obj q.overObj ⟶ X.functorOfPoints)
        simpa only [Category.assoc] using congrArg (fun z ↦ t ≫ z) hab)
  haveI : Subsingleton p.overObj.left :=
    inferInstanceAs (Subsingleton (Spec (.of p.K)))
  haveI : IsIntegral p.overObj.left :=
    inferInstanceAs (IsIntegral (Spec (.of p.K)))
  -- Represent the fibre product of the two field spectra over `X`.
  let hr := Functor.relativelyRepresentable.of_diag X.representableDiagonal q.hom
  let R : Over S := hr.pullback p.hom
  let a : R ⟶ q.overObj := hr.fst' p.hom
  let b : R ⟶ p.overObj := hr.snd p.hom
  have hR : IsPullback (yoneda.map a) (yoneda.map b) q.hom p.hom :=
    hr.isPullback' p.hom
  haveI : Mono (yoneda.map b) := hR.mono_snd_of_mono hmono
  haveI : Mono b := yoneda.mono_of_mono_map inferInstance
  haveI : Mono b.left := inferInstance
  -- The common extension supplies a point of this fibre product.
  let i : e.point.overObj ⟶ q.overObj :=
    Over.homMk e.right.schemeHom e.right.fac_structure
  let j : e.point.overObj ⟶ p.overObj :=
    Over.homMk e.left.schemeHom e.left.fac_structure
  have hij : yoneda.map i ≫ q.hom = yoneda.map j ≫ p.hom :=
    e.right.fac_hom.trans e.left.fac_hom.symm
  let lift : e.point.overObj ⟶ R := hr.lift' i j hij
  let x : R.left := lift.left (default : Spec (.of e.point.K))
  haveI : Subsingleton R.left :=
    ⟨fun x y ↦ b.left.injective (Subsingleton.elim _ _)⟩
  haveI : CompactSpace R.left := inferInstance
  haveI : Surjective b.left := ⟨fun y ↦ ⟨x, Subsingleton.elim _ _⟩⟩
  haveI : Flat b.left := inferInstance
  haveI : QuasiCompact b.left := inferInstance
  -- A nonempty monomorphism into a field spectrum is an isomorphism.
  haveI : IsIso b.left := Flat.isIso_of_surjective_of_mono b.left
  haveI : IsIso ((Over.forget S).map b) := by
    change IsIso b.left
    infer_instance
  haveI : IsIso b := isIso_of_reflects_iso b (Over.forget S)
  let f : p.overObj ⟶ q.overObj := inv b ≫ a
  refine ⟨⟨f.left, Over.w f, ?_⟩⟩
  change yoneda.map f ≫ q.hom = p.hom
  calc
    yoneda.map f ≫ q.hom =
        yoneda.map (inv b) ≫ (yoneda.map a ≫ q.hom) := by
      rw [Functor.map_comp, Category.assoc]
    _ = yoneda.map (inv b) ≫ (yoneda.map b ≫ p.hom) := by rw [hR.w]
    _ = p.hom := by
      rw [← Category.assoc, ← Functor.map_comp]
      simp

/-- Factorizations through a monomorphic field-valued point are unique. -/
theorem Factorization.subsingleton_of_mono {S : Scheme.{u}} {X : AlgebraicSpace S}
    {p q : FieldValuedPoint X} (hq : Mono q.hom) : Subsingleton (p.Factorization q) := by
  letI : Mono q.hom := hq
  refine ⟨fun φ ψ ↦ ?_⟩
  rcases φ with ⟨f, hf, hfx⟩
  rcases ψ with ⟨g, hg, hgx⟩
  have heq : f = g := congrArg (fun k : p.overObj ⟶ q.overObj ↦ k.left)
    (yoneda.map_injective ((cancel_mono q.hom).mp (hfx.trans hgx.symm)))
  cases heq
  rfl

/-- A field-valued point representing the same point as a monomorphic field-valued point
factors uniquely through it. -/
theorem unique_factorization_of_mono {S : Scheme.{u}} {X : AlgebraicSpace S}
    {p q : FieldValuedPoint X} (hq : Mono q.hom) (h : Points.mk p = Points.mk q) :
    Nonempty (p.Factorization q) ∧ Subsingleton (p.Factorization q) := by
  obtain ⟨e⟩ : Equivalent p q := Quotient.exact h
  exact ⟨Factorization.nonempty_of_commonExtension_of_mono hq e,
    Factorization.subsingleton_of_mono hq⟩

/-- A monomorphic field-valued point factors uniquely through any monomorphic field-valued
point representing the same point of the algebraic space. -/
theorem iso_unique_of_mono {S : Scheme.{u}} {X : AlgebraicSpace S}
    {p q : FieldValuedPoint X} [Mono p.hom] [Mono q.hom]
    (h : Points.mk p = Points.mk q) :
    Nonempty (p.Factorization q) ∧ Subsingleton (p.Factorization q) :=
  sorry

/-- Two monomorphic field-valued points determine the same point of `|X|` if and only
if one factors through the other. -/
theorem mk_eq_mk_iff_of_mono {S : Scheme.{u}} {X : AlgebraicSpace S}
    {p q : FieldValuedPoint X} [Mono p.hom] [Mono q.hom] :
    Points.mk p = Points.mk q ↔ Nonempty (p.Factorization q) :=
  sorry

/-- A factorization between monomorphic field-valued points is an isomorphism of
source spectra. -/
theorem Factorization.isIso_schemeHom_of_mono {S : Scheme.{u}} {X : AlgebraicSpace S}
    {p q : FieldValuedPoint X} [Mono p.hom] [Mono q.hom]
    (φ : p.Factorization q) : IsIso φ.schemeHom :=
  sorry

/-- Monomorphic field-valued points representing the same point of an algebraic space
are uniquely isomorphic over that algebraic space. -/
theorem unique_iso_of_mono {S : Scheme.{u}} {X : AlgebraicSpace S}
    {p q : FieldValuedPoint X} [Mono p.hom] [Mono q.hom]
    (h : Points.mk p = Points.mk q) :
    Nonempty (p ≅ q) ∧ Subsingleton (p ≅ q) :=
  sorry

end FieldValuedPoint

/-- For monomorphic field-valued points `p` of `X` and `q` of `Y`, a factorization of
`p.map f` through `q` is an isomorphism of source spectra if and only if the
composite `p.hom ≫ f` is a monomorphism. -/
theorem isIso_factorization_iff_mono_comp {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    {p : FieldValuedPoint X} {q : FieldValuedPoint Y} [Mono p.hom] [Mono q.hom]
    (f : X ⟶ Y) (φ : FieldValuedPoint.Factorization (p.map f) q) :
    IsIso φ.schemeHom ↔ Mono (p.hom ≫ f) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
