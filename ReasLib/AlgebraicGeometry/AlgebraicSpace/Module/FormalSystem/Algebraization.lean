/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.FormalSystem
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Pullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Pullback.Equality

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
      (_ : flatOver ℱ (SchemeRealization.toBase S.space))
      (_ : HasProperSupportOver (SchemeRealization.toBase S.space) ℱ)
      (e : ∀ n, (pullback (S.stageToSpace n)).obj ℱ ≅ S.moduleSheaf n),
      ∀ n,
        (pullback (S.stageMap n)).map (e (n + 1)).hom ≫ (S.moduleTransitionIso n).hom =
          (pullbackCompIso (S.stageMap n) (S.stageToSpace (n + 1))).hom.app ℱ ≫
            (pullbackCongr (S.stageMap_comp_stageToSpace n)).hom.app ℱ ≫ (e n).hom := sorry

end AlgebraicGeometry.AlgebraicSpace.Modules.ProperFlatFormalSystem
