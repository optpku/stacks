/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ZariskiCover.Basic
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.PropertyAlpha
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.PropertyBeta
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Decent
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Reasonable
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.VeryReasonable
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation.Absolute
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.IsScheme

/-!
# Zariski locality of conditions on algebraic spaces

These results state that the listed properties of an algebraic space descend
from an explicit Zariski covering.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u v

namespace AlgebraicGeometry.AlgebraicSpace

set_option backward.isDefEq.respectTransparency false in
/-- A covering member containing the unique point of a field spectrum pulls back to
the whole spectrum, so the field-valued point factors through that member. -/
private theorem fieldPoint_lifts_zariskiCover {S : Scheme.{u}} {X : AlgebraicSpace S}
    (𝒰 : ZariskiCover X) (p : FieldValuedPoint X) :
    ∃ i, ∃ q : ofOver p.overObj ⟶ 𝒰.X i, q ≫ 𝒰.f i = p.hom := by
  classical
  let 𝒱 := 𝒰.pullbackOpenCover p.hom
  let x : Spec (.of p.K) := (⊥ : PrimeSpectrum p.K)
  haveI : Subsingleton p.overObj.left :=
    inferInstanceAs (Subsingleton (PrimeSpectrum p.K))
  obtain ⟨i, y, hy⟩ := 𝒱.exists_eq x
  have hs : Function.Surjective (𝒱.f i) := by
    intro z
    exact ⟨y, hy.trans (Subsingleton.elim _ _)⟩
  haveI : Epi (𝒱.f i).base := (TopCat.epi_iff_surjective _).mpr hs
  haveI : IsIso (𝒱.f i) := AlgebraicGeometry.IsOpenImmersion.isIso _
  let b := (𝒰.isOpenImmersion i).presheaf.rep.snd p.hom
  haveI : IsIso ((Over.forget S).map b) := inferInstanceAs (IsIso (𝒱.f i))
  haveI : IsIso b := isIso_of_reflects_iso b (Over.forget S)
  let q : yoneda.obj p.overObj ⟶ (𝒰.X i).functorOfPoints :=
    yoneda.map (inv b) ≫ (𝒰.isOpenImmersion i).presheaf.rep.fst p.hom
  refine ⟨i, q, ?_⟩
  change (yoneda.map (inv b) ≫ (𝒰.isOpenImmersion i).presheaf.rep.fst p.hom) ≫
    (𝒰.f i : (𝒰.X i).functorOfPoints ⟶ X.functorOfPoints) = p.hom
  rw [Category.assoc, ((𝒰.isOpenImmersion i).presheaf.rep.isPullback p.hom).w,
    ← Category.assoc, ← yoneda.map_comp]
  change yoneda.map (inv b ≫ b) ≫ p.hom = p.hom
  rw [IsIso.inv_hom_id, CategoryTheory.Functor.map_id, Category.id_comp]

private theorem points_lift_zariskiCover {S : Scheme.{u}} {X : AlgebraicSpace S}
    (𝒰 : ZariskiCover X) (x : Points X) :
    ∃ i, ∃ y : Points (𝒰.X i), Points.map (𝒰.f i) y = x := by
  induction x using Quotient.inductionOn with
  | _ p =>
    obtain ⟨i, q, hq⟩ := fieldPoint_lifts_zariskiCover 𝒰 p
    refine ⟨i, Points.mk (FieldValuedPoint.of p.K p.structureHom q), ?_⟩
    change Points.mk (FieldValuedPoint.of p.K p.structureHom (q ≫ 𝒰.f i)) = Points.mk p
    rw [hq]
    rfl

private theorem points_map_comp_zariskiLocal {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (g : Y ⟶ Z) (x : Points X) :
    Points.map (f ≫ g) x = Points.map g (Points.map f x) := by
  induction x using Quotient.inductionOn with
  | _ p => rfl

namespace HasPropertyAlpha

/-- Property (α) descends along a Zariski covering of an algebraic space. -/
theorem of_zariskiCover {S : Scheme.{u}} {X : AlgebraicSpace S} (𝒰 : ZariskiCover X)
    [∀ i, HasPropertyAlpha (𝒰.X i)] : HasPropertyAlpha X :=
  sorry

end HasPropertyAlpha

namespace HasPropertyBeta

/-- Property (β) descends along a Zariski covering of an algebraic space. -/
theorem of_zariskiCover {S : Scheme.{u}} {X : AlgebraicSpace S} (𝒰 : ZariskiCover X)
    [∀ i, HasPropertyBeta (𝒰.X i)] : HasPropertyBeta X := by
  refine ⟨?_⟩
  intro x
  induction x using Quotient.inductionOn with
  | _ p =>
    obtain ⟨i, q, hq⟩ := fieldPoint_lifts_zariskiCover 𝒰 p
    let r : FieldValuedPoint (𝒰.X i) := FieldValuedPoint.of p.K p.structureHom q
    obtain ⟨r', hr', heq⟩ := HasPropertyBeta.exists_mono (X := 𝒰.X i) (Points.mk r)
    letI := hr'
    letI := 𝒰.mono i
    refine ⟨r'.map (𝒰.f i), inferInstanceAs (Mono (r'.hom ≫ 𝒰.f i)), ?_⟩
    obtain ⟨e⟩ : FieldValuedPoint.Equivalent r' r := Quotient.exact heq
    apply Quotient.sound
    refine ⟨{
      point := e.point.map (𝒰.f i)
      left := {
        schemeHom := e.left.schemeHom
        fac_structure := e.left.fac_structure
        fac_hom := ?_ }
      right := {
        schemeHom := e.right.schemeHom
        fac_structure := e.right.fac_structure
        fac_hom := ?_ } }⟩
    · change ofOverHomMk e.left.schemeHom e.left.fac_structure ≫
        (r'.hom ≫ 𝒰.f i) = e.point.hom ≫ 𝒰.f i
      exact congrArg (fun k ↦ k ≫ 𝒰.f i) e.left.fac_hom
    · change ofOverHomMk e.right.schemeHom e.right.fac_structure ≫ p.hom =
        e.point.hom ≫ 𝒰.f i
      rw [← hq]
      exact congrArg (fun k ↦ k ≫ 𝒰.f i) e.right.fac_hom

end HasPropertyBeta

namespace IsDecent

/-- Decency descends along a Zariski covering of an algebraic space. -/
theorem of_zariskiCover {S : Scheme.{u}} {X : AlgebraicSpace S} (𝒰 : ZariskiCover X)
    [∀ i, IsDecent (𝒰.X i)] : IsDecent X :=
  sorry

end IsDecent

namespace IsReasonable

/-- Reasonableness descends along a Zariski covering of an algebraic space. -/
theorem of_zariskiCover {S : Scheme.{u}} {X : AlgebraicSpace S} (𝒰 : ZariskiCover X)
    [∀ i, IsReasonable (𝒰.X i)] : IsReasonable X :=
  sorry

end IsReasonable

namespace IsVeryReasonable

/-- Very reasonableness descends along a Zariski covering of an algebraic space. -/
theorem of_zariskiCover {S : Scheme.{u}} {X : AlgebraicSpace S} (𝒰 : ZariskiCover X)
    [∀ i, IsVeryReasonable (𝒰.X i)] : IsVeryReasonable X := by
  classical
  letI := 𝒰.small
  letI : (MorphismProperty.over (@AlgebraicGeometry.Etale) :
      MorphismProperty (Over S)).IsStableUnderComposition := by
    change (MorphismProperty.inverseImage (@AlgebraicGeometry.Etale)
      (Over.forget S)).IsStableUnderComposition
    infer_instance
  choose J V p hp hc hr using fun i ↦ IsVeryReasonable.exists_cover (X := 𝒰.X i)
  let e := (equivShrink 𝒰.I₀).symm
  refine ⟨⟨(i : Shrink 𝒰.I₀) × J (e i), (fun a ↦ V (e a.1) a.2),
    (fun a ↦ p (e a.1) a.2 ≫ 𝒰.f (e a.1)), ?_, ?_, ?_⟩⟩
  · rintro ⟨i, j⟩
    have ho : (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf (𝒰.f (e i)) :=
      MorphismProperty.relative_monotone (P := MorphismProperty.over
        (@AlgebraicGeometry.IsOpenImmersion)) (fun U W g hg ↦ by
          haveI : AlgebraicGeometry.IsOpenImmersion g.left := hg
          exact inferInstanceAs (AlgebraicGeometry.Etale g.left)) _
        (𝒰.isOpenImmersion (e i)).presheaf
    refine ⟨fun a ha ↦ ?_⟩
    change (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf
      ((a ≫ p (e i) j) ≫ 𝒰.f (e i))
    exact ((MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf).comp_mem
      (a ≫ p (e i) j) (𝒰.f (e i))
      ((hp (e i) j).of_etale a ha) ho
  · apply Set.eq_univ_of_forall
    intro x
    obtain ⟨i, y, hy⟩ := points_lift_zariskiCover 𝒰 x
    obtain ⟨i, rfl⟩ := e.surjective i
    have hy' : y ∈ ⋃ j, Set.range (Points.map (p (e i) j)) := by
      rw [hc]
      trivial
    obtain ⟨j, z, hz⟩ := Set.mem_iUnion.mp hy'
    exact Set.mem_iUnion.mpr ⟨⟨i, j⟩, z,
      (points_map_comp_zariskiLocal _ _ _).trans
        ((congrArg (Points.map (𝒰.f (e i))) hz).trans hy)⟩
  · rintro ⟨i, j⟩
    obtain ⟨R, s, t, hst, hs, ht⟩ := hr (e i) j
    letI := 𝒰.mono (e i)
    exact ⟨R, s, t, IsPullback.of_isLimit
      (Limits.PullbackCone.isLimitOfCompMono _ _ (𝒰.f (e i)) _ hst.isLimit), hs, ht⟩

end IsVeryReasonable

namespace IsAbsolutelyZariskiLocallyQuasiSeparated

/-- Absolute Zariski-local quasi-separatedness descends along a Zariski covering. -/
theorem of_zariskiCover {S : Scheme.{u}} {X : AlgebraicSpace S} (𝒰 : ZariskiCover X)
    [∀ i, IsAbsolutelyZariskiLocallyQuasiSeparated (𝒰.X i)] :
    IsAbsolutelyZariskiLocallyQuasiSeparated X :=
  sorry

end IsAbsolutelyZariskiLocallyQuasiSeparated

namespace IsScheme

/-- Being a scheme descends along a Zariski covering of an algebraic space. -/
theorem of_zariskiCover {S : Scheme.{u}} {X : AlgebraicSpace S} (𝒰 : ZariskiCover X)
    [∀ i, IsScheme (𝒰.X i)] : IsScheme X :=
  sorry

end IsScheme

end AlgebraicGeometry.AlgebraicSpace
