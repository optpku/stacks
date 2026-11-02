/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RelativeSpectrum.Diagonal

/-!
# The represented diagonal with its actual lift operation

The invariant closed equality ideal supplies a concrete coincidence scheme.
Pointwise lifts to that native subscheme assemble into the limiting cone on
the original functor's diagonal. Every representability witness contains this
actual scheme and both specified projection maps.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} {X : AlgebraicSpace S} {T : Over S}

/-- The local equality ideal is invariant on the actual double overlap of the atlas cover. -/
theorem relativeSpectrumDiagonalLocalIdeal_invariant (A : X.QcAlgebraUnder)
    (p q : relativeSpectrumPair A T) :
    (relativeSpectrumDiagonalLocalIdeal A p q).comap
        (pullback.fst (relativeSpectrumDiagonalAtlasToBase A p q).left
          (relativeSpectrumDiagonalAtlasToBase A p q).left) =
      (relativeSpectrumDiagonalLocalIdeal A p q).comap
        (pullback.snd (relativeSpectrumDiagonalAtlasToBase A p q).left
          (relativeSpectrumDiagonalAtlasToBase A p q).left) := by
  rw [← relativeSpectrumDiagonalIdeal_comap A p q,
    ← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp,
    pullback.condition]

/-- The original pair of point transformations into the product of the spectrum functor. -/
def relativeSpectrumDiagonalPairNat (A : X.QcAlgebraUnder) (p q : relativeSpectrumPair A T) :
    yoneda.obj T ⟶ relativeSpectrumFunctor A ⨯ relativeSpectrumFunctor A :=
  prod.lift (yonedaEquiv.symm p) (yonedaEquiv.symm q)

/-- The coincidence scheme maps to the original spectrum functor through the first given point. -/
def relativeSpectrumDiagonalToFunctor (A : X.QcAlgebraUnder) (p q : relativeSpectrumPair A T) :
    yoneda.obj (relativeSpectrumDiagonalOver A p q) ⟶ relativeSpectrumFunctor A :=
  yoneda.map (relativeSpectrumDiagonalToTest A p q) ≫ yonedaEquiv.symm p

/-- The closed coincidence condition gives the diagonal square for the two supplied original points. -/
theorem relativeSpectrumDiagonalToFunctor_w (A : X.QcAlgebraUnder) (p q : relativeSpectrumPair A T) :
    relativeSpectrumDiagonalToFunctor A p q ≫ CategoryTheory.Limits.diag (relativeSpectrumFunctor A) =
      yoneda.map (relativeSpectrumDiagonalToTest A p q) ≫ relativeSpectrumDiagonalPairNat A p q := sorry

/-- The concrete represented diagonal cone, with its actual scheme and projection maps. -/
def relativeSpectrumDiagonalCone (A : X.QcAlgebraUnder) (p q : relativeSpectrumPair A T) :
    PullbackCone (CategoryTheory.Limits.diag (relativeSpectrumFunctor A)) (relativeSpectrumDiagonalPairNat A p q) :=
  PullbackCone.mk (relativeSpectrumDiagonalToFunctor A p q)
    (yoneda.map (relativeSpectrumDiagonalToTest A p q)) (relativeSpectrumDiagonalToFunctor_w A p q)

/-- The two restrictions prescribed by any cone point equal its actual spectrum-point component. -/
theorem relativeSpectrumDiagonalConePoint_eq (A : X.QcAlgebraUnder) (p q : relativeSpectrumPair A T)
    (c : PullbackCone (CategoryTheory.Limits.diag (relativeSpectrumFunctor A)) (relativeSpectrumDiagonalPairNat A p q))
    (W : (Over S)ᵒᵖ) (z : c.pt.obj W) :
    relativeSpectrumPairMap (c.snd.app W z) p = c.fst.app W z ∧
      relativeSpectrumPairMap (c.snd.app W z) q = c.fst.app W z := by
  have hp := congrArg (fun f ↦ f ≫ prod.fst) c.condition
  have hq := congrArg (fun f ↦ f ≫ prod.snd) c.condition
  simp only [relativeSpectrumDiagonalPairNat, Category.assoc, prod.lift_fst,
    prod.lift_snd, Category.comp_id] at hp hq
  exact ⟨(congrArg (fun f ↦ f.app W z) hp).symm,
    (congrArg (fun f ↦ f.app W z) hq).symm⟩

/-- The native closed lift has the prescribed projection to the original test scheme. -/
theorem relativeSpectrumDiagonalPointLift_toTest (A : X.QcAlgebraUnder)
    (p q : relativeSpectrumPair A T) {W : Over S} (a : W ⟶ T)
    (x : relativeSpectrumPair A W)
    (h : relativeSpectrumPairMap a p = x ∧ relativeSpectrumPairMap a q = x) :
    relativeSpectrumDiagonalPointLift A p q a x h ≫ relativeSpectrumDiagonalToTest A p q = a := by
  have hbase : relativeSpectrumDiagonalBaseLift A p q a x h ≫
      relativeSpectrumDiagonalBaseToTest A p q = a := by
    apply yoneda.map_injective
    simp only [Functor.map_comp, relativeSpectrumDiagonalBaseLift,
      relativeSpectrumDiagonalBaseToTest, Functor.map_preimage]
    exact (X.representableDiagonal.isPullback
      (prod.lift (relativeSpectrumPointBase A p) (relativeSpectrumPointBase A q))).lift_snd _ _ _
  apply Over.OverMorphism.ext
  change AlgebraicGeometry.IsClosedImmersion.lift _ _ _ ≫
    ((relativeSpectrumDiagonalIdeal A p q).subschemeι ≫
      (relativeSpectrumDiagonalBaseToTest A p q).left) = a.left
  rw [← Category.assoc, AlgebraicGeometry.IsClosedImmersion.lift_fac]
  exact congrArg (fun f ↦ f.left) hbase

/-- The coincidence scheme is a subobject of the original test scheme. -/
theorem relativeSpectrumDiagonalToTest_mono (A : X.QcAlgebraUnder)
    (p q : relativeSpectrumPair A T) : Mono (relativeSpectrumDiagonalToTest A p q) := by
  letI : Mono (yoneda.map (relativeSpectrumDiagonalBaseToTest A p q)) :=
    (X.representableDiagonal.isPullback
      (prod.lift (relativeSpectrumPointBase A p) (relativeSpectrumPointBase A q))).mono_snd_of_mono
  letI : Mono (relativeSpectrumDiagonalBaseToTest A p q) :=
    yoneda.mono_of_mono_map inferInstance
  letI : Mono (relativeSpectrumDiagonalToTest A p q).left := by
    change Mono ((relativeSpectrumDiagonalIdeal A p q).subschemeι ≫
      (relativeSpectrumDiagonalBaseToTest A p q).left)
    infer_instance
  exact Over.mono_of_mono_left _

/-- The mediating natural transformation consists of actual pointwise native closed-subscheme lifts. -/
def relativeSpectrumDiagonalConeLift (A : X.QcAlgebraUnder) (p q : relativeSpectrumPair A T)
    (c : PullbackCone (CategoryTheory.Limits.diag (relativeSpectrumFunctor A)) (relativeSpectrumDiagonalPairNat A p q)) :
    c.pt ⟶ yoneda.obj (relativeSpectrumDiagonalOver A p q) where
  app W := TypeCat.ofHom fun z ↦ relativeSpectrumDiagonalPointLift A p q
    (c.snd.app W z) (c.fst.app W z) (relativeSpectrumDiagonalConePoint_eq A p q c W z)
  naturality := by
    intro W W' f
    ext z
    letI := relativeSpectrumDiagonalToTest_mono A p q
    apply (cancel_mono (relativeSpectrumDiagonalToTest A p q)).1
    change relativeSpectrumDiagonalPointLift A p q _ _ _ ≫
        relativeSpectrumDiagonalToTest A p q =
      (f.unop ≫ relativeSpectrumDiagonalPointLift A p q _ _ _) ≫
        relativeSpectrumDiagonalToTest A p q
    rw [relativeSpectrumDiagonalPointLift_toTest, Category.assoc,
      relativeSpectrumDiagonalPointLift_toTest]
    exact c.snd.naturality_apply f z

/-- The pointwise lift recovers the given test-scheme component of a cone. -/
theorem relativeSpectrumDiagonalConeLift_toTest (A : X.QcAlgebraUnder)
    (p q : relativeSpectrumPair A T)
    (c : PullbackCone (CategoryTheory.Limits.diag (relativeSpectrumFunctor A))
      (relativeSpectrumDiagonalPairNat A p q)) :
    relativeSpectrumDiagonalConeLift A p q c ≫
      yoneda.map (relativeSpectrumDiagonalToTest A p q) = c.snd := by
  ext W z
  exact relativeSpectrumDiagonalPointLift_toTest A p q _ _ _

/-- The concrete diagonal cone is limiting with the specified actual pointwise lift function. -/
def relativeSpectrumDiagonalConeIsLimit (A : X.QcAlgebraUnder) (p q : relativeSpectrumPair A T) :
    IsLimit (relativeSpectrumDiagonalCone A p q) :=
  PullbackCone.IsLimit.mk (relativeSpectrumDiagonalToFunctor_w A p q)
    (relativeSpectrumDiagonalConeLift A p q)
    (by
      intro c
      rw [relativeSpectrumDiagonalToFunctor, ← Category.assoc,
        relativeSpectrumDiagonalConeLift_toTest]
      ext W z
      exact (relativeSpectrumDiagonalConePoint_eq A p q c W z).1)
    (relativeSpectrumDiagonalConeLift_toTest A p q)
    (by
      intro c m hfst hsnd
      letI := relativeSpectrumDiagonalToTest_mono A p q
      apply (cancel_mono (yoneda.map (relativeSpectrumDiagonalToTest A p q))).1
      exact hsnd.trans (relativeSpectrumDiagonalConeLift_toTest A p q c).symm)

/-- The diagonal of the original spectrum functor has an explicit scheme witness for every test pair. -/
theorem relativeSpectrumFunctor_representableDiagonal (A : X.QcAlgebraUnder) :
    yoneda.relativelyRepresentable (CategoryTheory.Limits.diag (relativeSpectrumFunctor A)) := by
  intro T g
  let p : relativeSpectrumPair A T := yonedaEquiv (g ≫ prod.fst)
  let q : relativeSpectrumPair A T := yonedaEquiv (g ≫ prod.snd)
  refine ⟨relativeSpectrumDiagonalOver A p q, relativeSpectrumDiagonalToTest A p q,
    relativeSpectrumDiagonalToFunctor A p q, ?_⟩
  have hp := IsPullback.of_isLimit (relativeSpectrumDiagonalConeIsLimit A p q)
  change IsPullback (relativeSpectrumDiagonalToFunctor A p q)
    (yoneda.map (relativeSpectrumDiagonalToTest A p q))
    (CategoryTheory.Limits.diag (relativeSpectrumFunctor A)) (relativeSpectrumDiagonalPairNat A p q) at hp
  have hpair : relativeSpectrumDiagonalPairNat A p q = g := by
    apply prod.hom_ext <;> simp only [relativeSpectrumDiagonalPairNat, prod.lift_fst,
      prod.lift_snd, p, q, Equiv.symm_apply_apply]
  exact hpair ▸ hp

end AlgebraicGeometry.AlgebraicSpace
