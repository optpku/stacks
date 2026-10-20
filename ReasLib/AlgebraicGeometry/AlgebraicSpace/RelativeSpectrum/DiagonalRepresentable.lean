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
          (relativeSpectrumDiagonalAtlasToBase A p q).left) := sorry

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
      relativeSpectrumPairMap (c.snd.app W z) q = c.fst.app W z := sorry

/-- The mediating natural transformation consists of actual pointwise native closed-subscheme lifts. -/
def relativeSpectrumDiagonalConeLift (A : X.QcAlgebraUnder) (p q : relativeSpectrumPair A T)
    (c : PullbackCone (CategoryTheory.Limits.diag (relativeSpectrumFunctor A)) (relativeSpectrumDiagonalPairNat A p q)) :
    c.pt ⟶ yoneda.obj (relativeSpectrumDiagonalOver A p q) where
  app W := TypeCat.ofHom fun z ↦ relativeSpectrumDiagonalPointLift A p q
    (c.snd.app W z) (c.fst.app W z) (relativeSpectrumDiagonalConePoint_eq A p q c W z)
  naturality := sorry

/-- The concrete diagonal cone is limiting with the specified actual pointwise lift function. -/
def relativeSpectrumDiagonalConeIsLimit (A : X.QcAlgebraUnder) (p q : relativeSpectrumPair A T) :
    IsLimit (relativeSpectrumDiagonalCone A p q) :=
  PullbackCone.IsLimit.mk (relativeSpectrumDiagonalToFunctor_w A p q)
    (relativeSpectrumDiagonalConeLift A p q) sorry sorry sorry

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
