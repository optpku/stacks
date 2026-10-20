/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.CoherentFormalModule.Algebraization.DepthThreeImprovement
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry
open scoped ENat

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.CoherentFormalModules

/- Lemma 52.21.3: in Situation 52.16.1, a dualizing complex, a bound on the
local cohomological dimension of `S.I`, and the `(2, 2 + d)`-inequalities yield a
depth-improved inverse system.  It is pro-isomorphic to a coherent formal module;
the induced map has uniformly `S.I`-power-annihilated kernels and cokernels, and
its degree-zero and degree-one cohomology modules at every stage are finite over `A`. -/
@[stacks 0EJG] #check
  (AlgebraicGeometry.Scheme.CoherentFormalModules.existsDepthThreeImprovement :
    ∀ {A : Type u} [CommRing A] [IsNoetherianRing A]
      (S : AffineAlgebraizationSetup A),
      (∃ K : DerivedCategory (ModuleCat.{u} A),
        CategoryTheory.DerivedCategory.IsDualizing K) →
      ∀ (d : ℤ), Ideal.LocalCohomology.HasDimensionLE S.I d →
      ∀ (F : CoherentFormalModules S.U.toScheme
        ((Scheme.idealSheafDataOfIdealOnSpec S.I).comap S.U.ι)),
      SatisfiesInequalities S F 2 (2 + d) →
      ∃ (F'' : SequentialInverseSystem (RingedSpace.Coh ((S.U.toScheme).toRingedSpace)))
        (α : F.obj ⟶ F''),
        IsDepthThreeImprovement S α ∧
          ∃ (H' : CoherentFormalModules S.U.toScheme
              ((Scheme.idealSheafDataOfIdealOnSpec S.I).comap S.U.ι))
            (e : (Pro.lim.{u + 1, u, 0, 0} ℕᵒᵖ).obj F'' ≅
              (Pro.lim.{u + 1, u, 0, 0} ℕᵒᵖ).obj H'.obj)
            (φ : F ⟶ H'),
            (Pro.lim.{u + 1, u, 0, 0} ℕᵒᵖ).map α ≫ e.hom =
                (Pro.lim.{u + 1, u, 0, 0} ℕᵒᵖ).map φ.hom ∧
              Scheme.CoherentFormalMap.StagesHaveUniformKernelCokernelAnnihilation
                ((Scheme.idealSheafDataOfIdealOnSpec S.I).comap S.U.ι) φ ∧
              ∀ n : ℕ,
                Module.Finite A
                    ((ModuleCat.restrictScalars (Scheme.Hom.globalSectionsMap S.U.ι)).obj
                      (Scheme.Modules.cohomology (F''.obj (op n)).obj 0)) ∧
                  Module.Finite A
                    ((ModuleCat.restrictScalars (Scheme.Hom.globalSectionsMap S.U.ι)).obj
                      (Scheme.Modules.cohomology (F''.obj (op n)).obj 1)))

end AlgebraicGeometry.Scheme.CoherentFormalModules
