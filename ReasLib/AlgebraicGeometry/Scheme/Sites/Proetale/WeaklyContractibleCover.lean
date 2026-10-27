/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import ReasLib.CategoryTheory.Sites.WeaklyContractible
public import ReasLib.CategoryTheory.Sites.MorphismProperty.Covering
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Proetale.ChosenPresentation
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Proetale.WeaklyContractible
public import ReasLib.AlgebraicGeometry.Scheme.Cover.Proetale.AffineWContractible

/-!
# Singleton weakly contractible covers in the pro-étale topology

Every object of the big, small, or slice pro-étale site admits a singleton
covering by a weakly contractible object. If the target is quasi-compact, that
covering object may be taken affine.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u v w

private theorem singleton_toPresieve {C : Type u} [Category.{v} C]
    {U V : C} (f : V ⟶ U) :
    (SemiRepresentableFamily.OverFamily.singleton.{v, u, w} f).toPresieve =
      Presieve.singleton f :=
  Presieve.ofArrows_pUnit f

private theorem coveringArrow_of_singleton_mem {C : Type u} [Category.{v} C]
    (K : Precoverage C) {U V : C} (f : V ⟶ U)
    (hf : (SemiRepresentableFamily.OverFamily.singleton.{v, u, w} f).toPresieve ∈ K U) :
    K.toGrothendieck.coveringArrows f := by
  rw [singleton_toPresieve] at hf
  simpa only [GrothendieckTopology.coveringArrows, CategoryTheory.Limits.FormalCoproduct.toSieve,
    singleton_toPresieve] using Precoverage.generate_mem_toGrothendieck hf

namespace AlgebraicGeometry.Scheme.Proetale

open CategoryTheory.Limits Opposite

private theorem isWeaklyContractible_sigma {ι : Type u} (V : ι → Scheme.{u})
    (hV : ∀ i, Scheme.proetaleTopology.IsWeaklyContractible (V i)) :
    Scheme.proetaleTopology.IsWeaklyContractible (∐ V) := by
  classical
  constructor
  intro F G pi hpi x
  have hZar : Scheme.zariskiTopology ≤ Scheme.proetaleTopology :=
    le_trans Scheme.zariskiTopology_le_etaleTopology Scheme.etaleTopology_le_proetaleTopology
  haveI : PreservesLimitsOfShape (Discrete ι) F.obj :=
    preservesLimitsOfShape_discrete_of_isSheaf_zariskiTopology
      ((isSheaf_iff_isSheaf_of_type _ _).mp (F.property.of_le hZar))
  haveI : PreservesLimitsOfShape (Discrete ι) G.obj :=
    preservesLimitsOfShape_discrete_of_isSheaf_zariskiTopology
      ((isSheaf_iff_isSheaf_of_type _ _).mp (G.property.of_le hZar))
  have hF := isLimitFanMkObjOfIsLimit F.obj (fun i ↦ op (V i))
    (fun i ↦ (Sigma.ι V i).op) (Cofan.IsColimit.op (coproductIsCoproduct V))
  have hG := isLimitFanMkObjOfIsLimit G.obj (fun i ↦ op (V i))
    (fun i ↦ (Sigma.ι V i).op) (Cofan.IsColimit.op (coproductIsCoproduct V))
  have hs (i : ι) : ∃ y, pi.hom.app (op (V i)) y = G.obj.map (Sigma.ι V i).op x :=
    (hV i).surjective_sections pi hpi _
  choose ys hys using hs
  let c : Fan (fun i ↦ F.obj.obj (op (V i))) :=
    Fan.mk PUnit (fun i ↦ ↾fun _ ↦ ys i)
  let y := hF.lift c PUnit.unit
  have hy (i : ι) : F.obj.map (Sigma.ι V i).op y = ys i :=
    ConcreteCategory.congr_hom (hF.fac c ⟨i⟩) PUnit.unit
  refine ⟨y, ?_⟩
  apply (Types.isLimitEquivSections hG).injective
  apply Subtype.ext
  funext i
  change G.obj.map (Sigma.ι V i.as).op (pi.hom.app (op (∐ V)) y) =
    G.obj.map (Sigma.ι V i.as).op x
  calc
    _ = pi.hom.app (op (V i.as)) (F.obj.map (Sigma.ι V i.as).op y) :=
      (ConcreteCategory.congr_hom (pi.hom.naturality (Sigma.ι V i.as).op) y).symm
    _ = _ := by rw [hy, hys]

/-- Every scheme admits a singleton family covering in the pro-étale
precoverage whose source is weakly contractible. -/
theorem exists_singleton_mem_proetalePrecoverage (U : Scheme.{u}) :
    ∃ (V : Scheme.{u}) (f : V ⟶ U),
      (SemiRepresentableFamily.OverFamily.singleton f).toPresieve ∈
          Scheme.proetalePrecoverage U ∧
        Scheme.proetaleTopology.IsWeaklyContractible V := by
  classical
  obtain ⟨𝒰, h𝒰⟩ := Scheme.Proetale.exists_affine_wContractibleRing_cover U
  let 𝒱 := 𝒰.forgetQc
  haveI (i : 𝒱.I₀) : IsAffine (𝒱.X i) := (h𝒰 i).1
  have hV (i : 𝒱.I₀) : Scheme.proetaleTopology.IsWeaklyContractible (𝒱.X i) :=
    IsWContractibleRing.iff_isWeaklyContractible_isAffine.mp (h𝒰 i).2
  refine ⟨∐ 𝒱.X, Sigma.desc 𝒱.f, ?_, isWeaklyContractible_sigma 𝒱.X hV⟩
  haveI : QuasiCompactCover 𝒱.sigma.toPreZeroHypercover :=
    .of_hom 𝒱.toSigma
  have hf : Presieve.singleton (Sigma.desc 𝒱.f) ∈ Scheme.proetalePrecoverage U := by
    rw [← 𝒱.presieve₀_sigma]
    exact (Scheme.Cover.ofQuasiCompactCover 𝒱.sigma).mem₀
  simpa only [singleton_toPresieve] using hf

/-- Every quasi-compact scheme admits a singleton family covering in the
pro-étale precoverage whose source is affine and weakly contractible. -/
theorem exists_singleton_mem_proetalePrecoverage_isAffine (U : Scheme.{u})
    [CompactSpace U] :
    ∃ (V : Scheme.{u}) (f : V ⟶ U),
      (SemiRepresentableFamily.OverFamily.singleton f).toPresieve ∈
          Scheme.proetalePrecoverage U ∧
        IsAffine V ∧ Scheme.proetaleTopology.IsWeaklyContractible V :=
  sorry

/-- Every scheme over `S` admits a singleton family covering in the pulled-back
pro-étale precoverage whose source is weakly contractible in the slice topology. -/
theorem exists_singleton_mem_proetalePrecoverage_over (S : Scheme.{u})
    (U : Over S) :
    ∃ (V : Over S) (f : V ⟶ U),
      (SemiRepresentableFamily.OverFamily.singleton f).toPresieve ∈
          (Scheme.proetalePrecoverage.comap (CategoryTheory.Over.forget S)) U ∧
        (Scheme.proetaleTopology.over S).IsWeaklyContractible V :=
  sorry

/-- Every quasi-compact scheme over `S` admits a singleton family covering in the
pulled-back pro-étale precoverage whose source is affine and weakly contractible
in the slice topology. -/
theorem exists_singleton_mem_proetalePrecoverage_isAffine_over (S : Scheme.{u})
    (U : Over S) [CompactSpace U.left] :
    ∃ (V : Over S) (f : V ⟶ U),
      (SemiRepresentableFamily.OverFamily.singleton f).toPresieve ∈
          (Scheme.proetalePrecoverage.comap (CategoryTheory.Over.forget S)) U ∧
        IsAffine V.left ∧
          (Scheme.proetaleTopology.over S).IsWeaklyContractible V :=
  sorry

/-- Every scheme admits a singleton covering arrow in the pro-étale topology
whose source is weakly contractible. -/
theorem exists_coveringArrow_isWeaklyContractible (U : Scheme.{u}) :
    ∃ (V : Scheme.{u}) (f : V ⟶ U),
      Scheme.proetaleTopology.coveringArrows f ∧
        Scheme.proetaleTopology.IsWeaklyContractible V := by
  obtain ⟨V, f, hf, hV⟩ := exists_singleton_mem_proetalePrecoverage.{u, 0} U
  exact ⟨V, f, coveringArrow_of_singleton_mem _ f hf, hV⟩

/-- Every quasi-compact scheme admits a singleton covering arrow in the
pro-étale topology whose source is affine and weakly contractible. -/
theorem exists_coveringArrow_isAffine_isWeaklyContractible (U : Scheme.{u})
    [CompactSpace U] :
    ∃ (V : Scheme.{u}) (f : V ⟶ U),
      Scheme.proetaleTopology.coveringArrows f ∧
        IsAffine V ∧ Scheme.proetaleTopology.IsWeaklyContractible V := by
  obtain ⟨V, f, hf, hV⟩ := exists_singleton_mem_proetalePrecoverage_isAffine.{u, 0} U
  exact ⟨V, f, coveringArrow_of_singleton_mem _ f hf, hV⟩

/-- Every scheme over `S` admits a singleton covering arrow in the slice
pro-étale topology whose source is weakly contractible. -/
theorem exists_coveringArrow_isWeaklyContractible_over (S : Scheme.{u})
    (U : Over S) :
    ∃ (V : Over S) (f : V ⟶ U),
      (Scheme.proetaleTopology.over S).coveringArrows f ∧
        (Scheme.proetaleTopology.over S).IsWeaklyContractible V := by
  obtain ⟨V, f, hf, hV⟩ := exists_singleton_mem_proetalePrecoverage_over.{u, 0} S U
  refine ⟨V, f, ?_, hV⟩
  rw [over_toGrothendieck_eq_toGrothendieck_comap_forget]
  exact coveringArrow_of_singleton_mem _ f hf

/-- Every quasi-compact scheme over `S` admits a singleton covering arrow in
the slice pro-étale topology whose source is affine and weakly contractible. -/
theorem exists_coveringArrow_isAffine_isWeaklyContractible_over (S : Scheme.{u})
    (U : Over S) [CompactSpace U.left] :
    ∃ (V : Over S) (f : V ⟶ U),
      (Scheme.proetaleTopology.over S).coveringArrows f ∧
        IsAffine V.left ∧
          (Scheme.proetaleTopology.over S).IsWeaklyContractible V := by
  obtain ⟨V, f, hf, hV⟩ := exists_singleton_mem_proetalePrecoverage_isAffine_over.{u, 0} S U
  refine ⟨V, f, ?_, hV⟩
  rw [over_toGrothendieck_eq_toGrothendieck_comap_forget]
  exact coveringArrow_of_singleton_mem _ f hf

end AlgebraicGeometry.Scheme.Proetale

namespace AlgebraicGeometry.Scheme.ProEt

/-- Every object of the small pro-étale site of `S` admits a singleton family
covering in the small pro-étale precoverage whose source is weakly
contractible. -/
theorem exists_singleton_mem_precoverage (S : Scheme.{u}) (U : S.ProEt) :
    ∃ (V : S.ProEt) (f : V ⟶ U),
      (SemiRepresentableFamily.OverFamily.singleton f).toPresieve ∈
          precoverage S U ∧
        (topology S).IsWeaklyContractible V :=
  sorry

/-- Every quasi-compact object of the small pro-étale site of `S` admits a
singleton family covering in the small pro-étale precoverage whose source is
affine and weakly contractible. -/
theorem exists_singleton_mem_precoverage_isAffine (S : Scheme.{u}) (U : S.ProEt)
    [CompactSpace U.left] :
    ∃ (V : S.ProEt) (f : V ⟶ U),
      (SemiRepresentableFamily.OverFamily.singleton f).toPresieve ∈
          precoverage S U ∧
        IsAffine V.left ∧ (topology S).IsWeaklyContractible V :=
  sorry

/-- Every object of the small pro-étale site of `S` admits a singleton covering
arrow whose source is weakly contractible. -/
theorem exists_coveringArrow_isWeaklyContractible (S : Scheme.{u}) (U : S.ProEt) :
    ∃ (V : S.ProEt) (f : V ⟶ U),
      (topology S).coveringArrows f ∧ (topology S).IsWeaklyContractible V := by
  obtain ⟨V, f, hf, hV⟩ := exists_singleton_mem_precoverage.{u, 0} S U
  exact ⟨V, f, coveringArrow_of_singleton_mem _ f hf, hV⟩

/-- Every quasi-compact object of the small pro-étale site of `S` admits a
singleton covering arrow whose source is affine and weakly contractible. -/
theorem exists_coveringArrow_isAffine_isWeaklyContractible (S : Scheme.{u})
    (U : S.ProEt) [CompactSpace U.left] :
    ∃ (V : S.ProEt) (f : V ⟶ U),
      (topology S).coveringArrows f ∧
        IsAffine V.left ∧ (topology S).IsWeaklyContractible V := by
  obtain ⟨V, f, hf, hV⟩ := exists_singleton_mem_precoverage_isAffine.{u, 0} S U
  exact ⟨V, f, coveringArrow_of_singleton_mem _ f hf, hV⟩

end AlgebraicGeometry.Scheme.ProEt

namespace AlgebraicGeometry.ChosenBigProetaleSite

/-- Every object of a chosen big pro-étale site admits a singleton covering
arrow whose source is weakly contractible. -/
theorem exists_coveringArrow_isWeaklyContractible
    (X : ChosenBigProetaleSite.{u, v}) (T : X.carrier) :
    ∃ (V : X.carrier) (f : V ⟶ T),
      X.toGrothendieck.coveringArrows f ∧
        X.toGrothendieck.IsWeaklyContractible V :=
  sorry

/-- Every quasi-compact object of a chosen big pro-étale site admits a singleton
covering arrow whose source is affine and weakly contractible. -/
theorem exists_coveringArrow_isAffine_isWeaklyContractible
    (X : ChosenBigProetaleSite.{u, v}) (T : X.carrier)
    [CompactSpace (X.toScheme.obj T)] :
    ∃ (V : X.carrier) (f : V ⟶ T),
      X.toGrothendieck.coveringArrows f ∧
        IsAffine (X.toScheme.obj V) ∧
          X.toGrothendieck.IsWeaklyContractible V :=
  sorry

/-- Every object of a chosen big pro-étale slice admits a singleton covering
arrow whose source is weakly contractible. -/
theorem exists_coveringArrow_isWeaklyContractible_big
    (X : ChosenBigProetaleSite.{u, v}) (S : X.carrier) (U : Over S) :
    ∃ (V : Over S) (f : V ⟶ U),
      (bigTopology X S).coveringArrows f ∧
        (bigTopology X S).IsWeaklyContractible V :=
  sorry

/-- Every quasi-compact object of a chosen big pro-étale slice admits a singleton
covering arrow whose source is affine and weakly contractible. -/
theorem exists_coveringArrow_isAffine_isWeaklyContractible_big
    (X : ChosenBigProetaleSite.{u, v}) (S : X.carrier) (U : Over S)
    [CompactSpace (X.toScheme.obj U.left)] :
    ∃ (V : Over S) (f : V ⟶ U),
      (bigTopology X S).coveringArrows f ∧
        IsAffine (X.toScheme.obj V.left) ∧
          (bigTopology X S).IsWeaklyContractible V :=
  sorry

/-- Every object of a chosen small pro-étale site admits a singleton covering
arrow whose source is weakly contractible. -/
theorem exists_coveringArrow_isWeaklyContractible_small
    (X : ChosenBigProetaleSite.{u, v}) (S : X.carrier) (U : smallSite X S) :
    ∃ (V : smallSite X S) (f : V ⟶ U),
      (smallTopology X S).coveringArrows f ∧
        (smallTopology X S).IsWeaklyContractible V :=
  sorry

/-- Every quasi-compact object of a chosen small pro-étale site admits a
singleton covering arrow whose source is affine and weakly contractible. -/
theorem exists_coveringArrow_isAffine_isWeaklyContractible_small
    (X : ChosenBigProetaleSite.{u, v}) (S : X.carrier) (U : smallSite X S)
    [CompactSpace (X.toScheme.obj U.obj.left)] :
    ∃ (V : smallSite X S) (f : V ⟶ U),
      (smallTopology X S).coveringArrows f ∧
        IsAffine (X.toScheme.obj V.obj.left) ∧
          (smallTopology X S).IsWeaklyContractible V :=
  sorry

end AlgebraicGeometry.ChosenBigProetaleSite
