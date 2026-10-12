/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Perfect.Determinant
public import stacks_project.Chap57.Definition_57_15_1_Kernel
public import stacks_project.Chap57.Lemma_57_8_2
public import stacks_project.Chap57.Lemma_57_15_2_Perfect

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

/-- Lemma 57.15.2 (1): if `K` is the Fourier--Mukai kernel of a relative
equivalence from `X` to `Y` over `S`, then the corresponding Fourier--Mukai
functor `Φ_K : D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_Y)` of Lemma 57.8.2 is an equivalence. -/
@[stacks 0G0J, instance]
instance FourierMukaiObject.quasicoherentFunctor_isEquivalence
    {S : Scheme.{u}} {X Y : FourierMukaiObject S}
    (K : @RingedSpace.ModuleDerived.Perfect
      (Limits.pullback X.hom Y.hom).toRingedSpace)
    [FourierMukaiObject.IsRelativeEquivalenceKernel K]
    [Scheme.Hom.FinitePresentation X.hom] [Flat X.hom] :
    (Scheme.FourierMukai.quasicoherent X.hom Y.hom
      ((Scheme.PerfectDerived.toDerivedQCoh
        (Limits.pullback X.hom Y.hom)).obj K)).IsEquivalence := sorry

/-- Lemma 57.15.2 (2): if `K` is the Fourier--Mukai kernel of a relative
equivalence from `X` to `Y` over `S`, then the corresponding Fourier--Mukai
functor `Φ_K : D_perf(𝒪_X) ⥤ D_perf(𝒪_Y)` of Lemma 57.8.4 is an equivalence. -/
@[stacks 0G0J, instance]
instance FourierMukaiObject.perfectFunctor_isEquivalence
    {S : Scheme.{u}} {X Y : FourierMukaiObject S}
    (K : @RingedSpace.ModuleDerived.Perfect
      (Limits.pullback X.hom Y.hom).toRingedSpace)
    [FourierMukaiObject.IsRelativeEquivalenceKernel K]
    [Scheme.Hom.FinitePresentation X.hom] [Flat X.hom] :
    (Scheme.FourierMukai.perfect X.hom Y.hom K).IsEquivalence := sorry
