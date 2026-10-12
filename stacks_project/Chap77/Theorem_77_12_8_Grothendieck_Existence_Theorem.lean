/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap77.Theorem_77_12_8_Grothendieck_Existence_Theorem_Algebraization
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules

noncomputable section

universe u

/- Theorem 77.12.8 (Grothendieck Existence Theorem): in Situation 77.12.1 there
exists a finitely presented 𝒪_X-module ℱ, flat over A, with support proper over A,
such that ℱ_n = ℱ ⊗_{𝒪_X} 𝒪_{X_n} for all n, encoded as the pullback isomorphism
`e n : (pullback (S.stageToSpace n)).obj ℱ ≅ S.moduleSheaf n`, compatibly with the
maps φ_n via the `pullbackComp`/`pullbackCongr` triangle against
`S.moduleTransitionIso n`. -/
@[stacks 0CXB] #check
  (AlgebraicGeometry.AlgebraicSpace.Modules.ProperFlatFormalSystem.existsAlgebraization :
    ∀ (S : AlgebraicGeometry.AlgebraicSpace.Modules.ProperFlatFormalSystem.{u}),
      ∃ (ℱ : S.space.Modules)
        (_ : ℱ.IsFinitePresentation)
        (_ : ∀ x, AlgebraicGeometry.AlgebraicSpace.Modules.flatOverAt ℱ (toBase S.space) x)
        (_ : AlgebraicGeometry.AlgebraicSpace.Modules.HasProperSupportOver (toBase S.space) ℱ)
        (e : ∀ n, (AlgebraicGeometry.AlgebraicSpace.Modules.pullback (S.stageToSpace n)).obj ℱ ≅
          S.moduleSheaf n),
        ∀ n,
          (AlgebraicGeometry.AlgebraicSpace.Modules.pullback (S.stageMap n)).map (e (n + 1)).hom ≫
              (S.moduleTransitionIso n).hom =
            (AlgebraicGeometry.AlgebraicSpace.Modules.pullbackComp
                (S.stageMap n) (S.stageToSpace (n + 1))).hom.app ℱ ≫
              (AlgebraicGeometry.AlgebraicSpace.Modules.pullbackCongr
                (S.stageMap_comp_stageToSpace n)).hom.app ℱ ≫ (e n).hom)
