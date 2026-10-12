/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Module.FormalSystem.Algebraization

@[expose] public section

open CategoryTheory

noncomputable section

universe u

/- Theorem 38.28.9 (Grothendieck Existence Theorem): a proper flat formal system of
modules comes from a finitely presented module on the limit scheme that is flat with proper
support over the limit base, compatibly with every finite stage. -/
@[stacks 0CTK] #check
  (AlgebraicGeometry.Scheme.Modules.ProperFlatFormalSystem.existsAlgebraization :
    ∀ (S : AlgebraicGeometry.Scheme.Modules.ProperFlatFormalSystem.{u}),
      ∃ (G : S.scheme.Modules)
        (_ : G.IsFinitePresentation)
        (_ : AlgebraicGeometry.Scheme.Modules.flatOver G S.structureMap)
        (_ : AlgebraicGeometry.Scheme.Modules.HasProperSupportOver S.structureMap G)
        (e : ∀ n, (AlgebraicGeometry.Scheme.Modules.pullback (S.stageToScheme n)).obj G ≅
          S.moduleSheaf n),
        ∀ n,
          (AlgebraicGeometry.Scheme.Modules.pullback (S.stageMap n)).map (e (n + 1)).hom ≫
              (S.moduleTransitionIso n).hom =
            (AlgebraicGeometry.Scheme.Modules.pullbackComp
                (S.stageMap n) (S.stageToScheme (n + 1))).hom.app G ≫
              (AlgebraicGeometry.Scheme.Modules.pullbackCongr
                (S.stageMap_comp_stageToScheme n)).hom.app G ≫ (e n).hom)
