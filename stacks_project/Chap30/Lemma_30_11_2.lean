/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Depth.InternalHom
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.MonoidalClosed
open scoped ENat

universe u

/- Lemma 30.11.2 (1): if the stalk `𝒢ₓ` has depth at least one, then the stalk of the internal
Hom sheaf from `ℱ` to `𝒢` has depth at least one. -/
@[stacks 0EBC] #check
  (@AlgebraicGeometry.Scheme.Modules.moduleDepth_internalHom_stalk_ge_one_of_moduleDepth_stalk_ge_one :
    ∀ {X : Scheme.{u}} [IsLocallyNoetherian X]
      {ℱ 𝒢 : X.Modules} [ℱ.IsCoherent] [𝒢.IsCoherent]
      (x : X)
      (h𝒢x : (1 : ℕ∞) ≤
        moduleDepth (X.presheaf.stalk x) (RingedSpace.stalkModuleCat 𝒢 x)),
      (1 : ℕ∞) ≤
        moduleDepth (X.presheaf.stalk x)
          (RingedSpace.stalkModuleCat ((ihom ℱ).obj 𝒢) x))

/- Lemma 30.11.2 (2): if the stalk `𝒢ₓ` has depth at least two, then the stalk of the internal
Hom sheaf from `ℱ` to `𝒢` has depth at least two. -/
@[stacks 0EBC] #check
  (@AlgebraicGeometry.Scheme.Modules.moduleDepth_internalHom_stalk_ge_two_of_moduleDepth_stalk_ge_two :
    ∀ {X : Scheme.{u}} [IsLocallyNoetherian X]
      {ℱ 𝒢 : X.Modules} [ℱ.IsCoherent] [𝒢.IsCoherent]
      (x : X)
      (h𝒢x : (2 : ℕ∞) ≤
        moduleDepth (X.presheaf.stalk x) (RingedSpace.stalkModuleCat 𝒢 x)),
      (2 : ℕ∞) ≤
        moduleDepth (X.presheaf.stalk x)
          (RingedSpace.stalkModuleCat ((ihom ℱ).obj 𝒢) x))
