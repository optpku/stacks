module

public import stacks_project.Chap70.Lemma_70_7_2_FinitePresentation
public import stacks_project.Chap77.Situation_77_12_1_FormalSystem

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules.ProperFlatFormalSystem

/-- A proper flat formal system of modules on an algebraic space algebraizes to a
finitely presented module on the limit space that is flat with proper support over
the limit base, and compatible with every finite stage. -/
theorem existsAlgebraization (S : ProperFlatFormalSystem.{u}) :
    ∃ (ℱ : S.space.Modules)
      (_ : ℱ.IsFinitePresentation)
      (_ : ∀ x, flatOverAt ℱ (toBase S.space) x)
      (_ : HasProperSupportOver (toBase S.space) ℱ)
      (e : ∀ n, (pullback (S.stageToSpace n)).obj ℱ ≅ S.moduleSheaf n),
      ∀ n,
        (pullback (S.stageMap n)).map (e (n + 1)).hom ≫ (S.moduleTransitionIso n).hom =
          (pullbackComp (S.stageMap n) (S.stageToSpace (n + 1))).hom.app ℱ ≫
            (pullbackCongr (S.stageMap_comp_stageToSpace n)).hom.app ℱ ≫ (e n).hom := sorry

end AlgebraicGeometry.AlgebraicSpace.Modules.ProperFlatFormalSystem
