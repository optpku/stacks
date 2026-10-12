/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Order.WithBotTop
public import ReasLib.Algebra.Homology.DerivedCategory.LocalCohomology.CohomologicalDimension
public import ReasLib.AlgebraicGeometry.Scheme.CoherentFormalModule.Algebraization.DepthOneImprovement
public import ReasLib.AlgebraicGeometry.Scheme.Module.Depth.ImprovementAlong

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry
open scoped ENat

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.CoherentFormalModules

/-- Under the completed-local depth, cohomological-dimension, and specialization
hypotheses on `T' ⊆ T ⊆ V(I)`, a coherent formal module admits a stagewise depth
improvement along `T' ⊆ T`, pro-isomorphic to a coherent formal module with
uniformly `I`-power-annihilated kernels and cokernels. -/
theorem existsDepthTwoImprovement {X : Scheme.{u}} [IsNoetherian X]
    (I : X.IdealSheafData) (F : CoherentFormalModules X I)
    (T' T : Set X) (hT' : StableUnderSpecialization T')
    (hT : StableUnderSpecialization T) (hTT' : T' ⊆ T)
    (hTY : T ⊆ Set.range I.subschemeι)
    (hdual : LocallyHasDualizingComplex X)
    (d : ℤ) (hd : 0 ≤ d)
    (h_cd : ∀ x : X, ∃ U : X.affineOpens,
      x ∈ (U : X.Opens) ∧
        Ideal.LocalCohomology.HasDimensionLE (I.ideal U) d)
    (hdepth_one : ∀ y : X, y ∈ T →
      let A_y := X.presheaf.stalk y
      let I_y : Ideal A_y :=
        RingedSpace.idealSheafStalkIdeal I.toSubobject y
      let M_y : ModuleCat A_y :=
        limit (F.obj ⋙ (SheafOfModules.isCoherent X.toRingedSpace.ringCatSheaf).ι ⋙
          X.toRingedSpace.stalkModuleFunctor y)
      let Ahat_y := AdicCompletion I_y A_y
      let Mhat_y : ModuleCat Ahat_y :=
        @ModuleCat.of Ahat_y _ M_y _
          (@IsAdicComplete.completedModule A_y _ I_y M_y _ _
            (stalkLimit_isAdicComplete_of_coherentFormalModule I F y))
      let Ihat_y : Ideal Ahat_y := I_y.map (algebraMap A_y Ahat_y)
      let mhat_y : Ideal Ahat_y :=
        (IsLocalRing.maximalIdeal A_y).map (algebraMap A_y Ahat_y)
      ∀ p : PrimeSpectrum Ahat_y, ¬ p.asIdeal.IsMaximal →
        PrimeSpectrum.zeroLocus p.asIdeal ∩
            PrimeSpectrum.zeroLocus (Ihat_y : Set Ahat_y) =
          {q | q.asIdeal = mhat_y} →
        0 < moduleDepth (Localization.AtPrime p.asIdeal)
          (LocalizedModule.AtPrime p.asIdeal Mhat_y))
    (hdepth_alt : ∀ y : X, y ∈ T' →
      let A_y := X.presheaf.stalk y
      let I_y : Ideal A_y :=
        RingedSpace.idealSheafStalkIdeal I.toSubobject y
      let M_y : ModuleCat A_y :=
        limit (F.obj ⋙ (SheafOfModules.isCoherent X.toRingedSpace.ringCatSheaf).ι ⋙
          X.toRingedSpace.stalkModuleFunctor y)
      let Ahat_y := AdicCompletion I_y A_y
      let Mhat_y : ModuleCat Ahat_y :=
        @ModuleCat.of Ahat_y _ M_y _
          (@IsAdicComplete.completedModule A_y _ I_y M_y _ _
            (stalkLimit_isAdicComplete_of_coherentFormalModule I F y))
      let Ihat_y : Ideal Ahat_y := I_y.map (algebraMap A_y Ahat_y)
      let mhat_y : Ideal Ahat_y :=
        (IsLocalRing.maximalIdeal A_y).map (algebraMap A_y Ahat_y)
      ∀ p : PrimeSpectrum Ahat_y,
        p ∉ PrimeSpectrum.zeroLocus (Ihat_y : Set Ahat_y) →
        PrimeSpectrum.zeroLocus p.asIdeal ∩
            PrimeSpectrum.zeroLocus (Ihat_y : Set Ahat_y) ≠
          {q | q.asIdeal = mhat_y} →
        (1 : EInt) ≤
            ((WithTop.map Int.ofNat
              (moduleDepth (Localization.AtPrime p.asIdeal)
                (LocalizedModule.AtPrime p.asIdeal Mhat_y)) : WithTop ℤ) : EInt) ∨
          ((d + 1 : ℤ) : EInt) <
            ((WithTop.map Int.ofNat
              (moduleDepth (Localization.AtPrime p.asIdeal)
                (LocalizedModule.AtPrime p.asIdeal Mhat_y)) : WithTop ℤ) : EInt) +
              WithBot.map (WithTop.map Int.ofNat)
                (ringKrullDim (Ahat_y ⧸ p.asIdeal)))
    (hdepth_two : ∀ y : X, y ∈ T' →
      let A_y := X.presheaf.stalk y
      let I_y : Ideal A_y :=
        RingedSpace.idealSheafStalkIdeal I.toSubobject y
      let M_y : ModuleCat A_y :=
        limit (F.obj ⋙ (SheafOfModules.isCoherent X.toRingedSpace.ringCatSheaf).ι ⋙
          X.toRingedSpace.stalkModuleFunctor y)
      let Ahat_y := AdicCompletion I_y A_y
      let Mhat_y : ModuleCat Ahat_y :=
        @ModuleCat.of Ahat_y _ M_y _
          (@IsAdicComplete.completedModule A_y _ I_y M_y _ _
            (stalkLimit_isAdicComplete_of_coherentFormalModule I F y))
      let Ihat_y : Ideal Ahat_y := I_y.map (algebraMap A_y Ahat_y)
      let mhat_y : Ideal Ahat_y :=
        (IsLocalRing.maximalIdeal A_y).map (algebraMap A_y Ahat_y)
      ∀ p : PrimeSpectrum Ahat_y, ¬ p.asIdeal.IsMaximal →
        PrimeSpectrum.zeroLocus p.asIdeal ∩
            PrimeSpectrum.zeroLocus (Ihat_y : Set Ahat_y) =
          {q | q.asIdeal = mhat_y} →
        (1 : EInt) <
          ((WithTop.map Int.ofNat
            (moduleDepth (Localization.AtPrime p.asIdeal)
              (LocalizedModule.AtPrime p.asIdeal Mhat_y)) : WithTop ℤ) : EInt))
    (h_immediate : ∀ ⦃y y' : X⦄,
      IsImmediateSpecialization y y' → y' ∈ T' → y ∈ T) :
    ∃ (F'' : SequentialInverseSystem (RingedSpace.Coh X.toRingedSpace))
        (α : F.obj ⟶ F''),
      (∀ n : ℕ,
        Scheme.Modules.IsDepthImprovementAlong T' T (α.app (op n)).hom) ∧
        ∃ (H : CoherentFormalModules X I)
            (e : (Pro.lim.{u + 1, u, 0, 0} ℕᵒᵖ).obj F'' ≅
              (Pro.lim.{u + 1, u, 0, 0} ℕᵒᵖ).obj H.obj)
            (φ : F ⟶ H),
          (Pro.lim.{u + 1, u, 0, 0} ℕᵒᵖ).map α ≫ e.hom =
              (Pro.lim.{u + 1, u, 0, 0} ℕᵒᵖ).map φ.hom ∧
            Scheme.CoherentFormalMap.StagesHaveUniformKernelCokernelAnnihilation I φ := sorry

end AlgebraicGeometry.Scheme.CoherentFormalModules
