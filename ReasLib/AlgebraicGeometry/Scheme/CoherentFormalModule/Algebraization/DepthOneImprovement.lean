/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import ReasLib.AlgebraicGeometry.Scheme.CoherentFormalModule.Completion.StalkLimit
public import ReasLib.AlgebraicGeometry.Scheme.CoherentFormalModule.MapAnnihilation
public import ReasLib.AlgebraicGeometry.Scheme.Module.DepthOneQuotient
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Dualizing.LocalExistence
public import ReasLib.CategoryTheory.Pro.Presentation
public import ReasLib.RingTheory.Depth.Localization

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry
open scoped ENat

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.CoherentFormalModules

/-- On a Noetherian scheme locally admitting dualizing complexes, positive completed-local
depth at nonmaximal primes meeting the completed defining ideal only at the maximal ideal
along a specialization-stable subset gives a stagewise depth-one quotient system. The quotient
system is pro-isomorphic to a coherent formal module, compatibly with an epic formal morphism
whose stage kernels and cokernels are uniformly annihilated by a power of the defining ideal. -/
theorem existsDepthOneImprovement {X : Scheme.{u}} [IsNoetherian X]
    (I : X.IdealSheafData) (F : CoherentFormalModules X I)
    (T : Set X) (hT : StableUnderSpecialization T)
    (hTY : T ⊆ Set.range I.subschemeι)
    (hdual : LocallyHasDualizingComplex X)
    (hdepth : ∀ y : X, (hyT : y ∈ T) →
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
          (LocalizedModule.AtPrime p.asIdeal Mhat_y)) :
    ∃ (F' : SequentialInverseSystem (RingedSpace.Coh X.toRingedSpace))
        (α : F.obj ⟶ F'),
      (∀ n : ℕ, Scheme.Modules.IsDepthOneQuotient T (α.app (op n)).hom) ∧
        ∃ (G : CoherentFormalModules X I)
            (e : (Pro.lim.{u + 1, u, 0, 0} ℕᵒᵖ).obj F' ≅
              (Pro.lim.{u + 1, u, 0, 0} ℕᵒᵖ).obj G.obj)
            (φ : F ⟶ G),
          (Pro.lim.{u + 1, u, 0, 0} ℕᵒᵖ).map α ≫ e.hom =
              (Pro.lim.{u + 1, u, 0, 0} ℕᵒᵖ).map φ.hom ∧
            Epi φ ∧
              Scheme.CoherentFormalMap.StagesHaveUniformKernelCokernelAnnihilation I φ := sorry

end AlgebraicGeometry.Scheme.CoherentFormalModules
