/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.DirectImage.Stalk
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace

universe u

/- Lemma 81.10.3. The geometric stalk of the direct image of a quasi-coherent module
along a quasi-compact and quasi-separated morphism is the module of sections on
the base change to the spectrum of the étale local ring. -/
@[stacks 0AES] #check (AlgebraicGeometry.AlgebraicSpace.Modules.pushforward_stalk_iso :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : Y ⟶ X)
    [QuasiCompact f] [QuasiSeparated f] (xbar : GeometricPoint X)
    (G : Y.Modules) [G.IsQuasicoherent],
    CategoryTheory.IsIsomorphic
      (AlgebraicGeometry.AlgebraicSpace.Modules.stalkModuleCat xbar
        ((AlgebraicGeometry.AlgebraicSpace.Modules.pushforward f).obj G))
      (AlgebraicGeometry.AlgebraicSpace.Modules.sectionsOverEtaleLocalRing f xbar G))
