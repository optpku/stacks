module

public import ReasLib.AlgebraicGeometry.Scheme.Module.FormalSystem
import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.FormalCompletion.ProperSupport
import ReasLib.AlgebraicGeometry.Scheme.Limit.Infinitesimal

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules.ProperFlatFormalSystem

/-- A proper flat formal system of modules admits an algebraization on its limit scheme that is
finitely presented, flat with proper support over the limit base, and compatible with every
finite stage. -/
theorem existsAlgebraization (S : ProperFlatFormalSystem.{u}) :
    ∃ (G : S.scheme.Modules)
      (_ : G.IsFinitePresentation)
      (_ : flatOver G S.structureMap)
      (_ : HasProperSupportOver S.structureMap G)
      (e : ∀ n, (pullback (S.stageToScheme n)).obj G ≅ S.moduleSheaf n),
      ∀ n,
        (pullback (S.stageMap n)).map (e (n + 1)).hom ≫ (S.moduleTransitionIso n).hom =
          (pullbackComp (S.stageMap n) (S.stageToScheme (n + 1))).hom.app G ≫
            (pullbackCongr (S.stageMap_comp_stageToScheme n)).hom.app G ≫ (e n).hom := sorry

end AlgebraicGeometry.Scheme.Modules.ProperFlatFormalSystem
