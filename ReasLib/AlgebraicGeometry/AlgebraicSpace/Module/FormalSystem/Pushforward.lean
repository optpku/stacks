/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.FormalSystem
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.DirectImage
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Pullback

/-!
# Pushforward of formal-system stage modules

Stage modules are viewed on the ambient algebraic space by pushforward along
their closed immersions.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules.ProperFlatFormalSystem

/-- The stage module sheaf `ℱ n`, viewed as a sheaf on `X` by pushforward along the
closed immersion `stageToSpace n : X_n ⟶ X`. -/
def pushforwardModule (S : ProperFlatFormalSystem) (n : ℕ) : S.space.Modules :=
  (Modules.pushforward (S.stageToSpace n)).obj (S.moduleSheaf n)

/-- `pushforwardModule` is the underived pushforward of the stage module sheaf along
the closed immersion to the limit space. -/
theorem pushforwardModule_spec (S : ProperFlatFormalSystem) (n : ℕ) :
    S.pushforwardModule n = (Modules.pushforward (S.stageToSpace n)).obj (S.moduleSheaf n) :=
  rfl

/-- The successor map of pushed stage sheaves, obtained by adjoining the stage
transition isomorphism, composing the iterated pushforward, and transporting along
`stageMap_comp_stageToSpace`. -/
def pushforwardStep (S : ProperFlatFormalSystem) (n : ℕ) :
    S.pushforwardModule (n + 1) ⟶ S.pushforwardModule n :=
  (Modules.pushforward (S.stageToSpace (n + 1))).map
      (((Modules.pullbackPushforwardAdjunction (S.stageMap n)).homEquiv
          (S.moduleSheaf (n + 1)) (S.moduleSheaf n)) (S.moduleTransitionIso n).hom) ≫
    (Modules.pushforwardComp (S.stageMap n) (S.stageToSpace (n + 1))).hom.app
      (S.moduleSheaf n) ≫
    eqToHom (congrArg (fun g : S.stageSpace n ⟶ S.space ↦
      (Modules.pushforward g).obj (S.moduleSheaf n)) (S.stageMap_comp_stageToSpace n))

end AlgebraicGeometry.AlgebraicSpace.Modules.ProperFlatFormalSystem
