/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Ideal.Pushforward
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RingedSite.Hom
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace AlgebraicGeometry.AlgebraicSpace.Modules
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

/-
Lemma 70.14.4: let `S` be a scheme and `f : X ⟶ Y` a quasi-compact and quasi-separated
morphism of algebraic spaces over `S`. Let `I ⊂ 𝒪_Y` be a quasi-coherent sheaf of ideals of
finite type. Let `ℱ` be a quasi-coherent `𝒪_X`-module, and let `ℱ' ⊂ ℱ` be the subsheaf of
sections annihilated by `f⁻¹I 𝒪_X`, namely `idealTorsionSubsheaf (I.pullback f) ℱ`. Then
`f_* ℱ' ⊂ f_* ℱ` is the subsheaf of sections annihilated by `I`.
-/
@[stacks 0858]
#check (AlgebraicGeometry.AlgebraicSpace.Modules.range_pushforward_idealTorsionSubsheafι_app_eq :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    (I : IdealSubobject Y) [(I : Y.Modules).IsQuasicoherent] [(I : Y.Modules).IsFiniteType]
    (ℱ : X.Modules) [ℱ.IsQuasicoherent] (U : smallEtaleSite Y),
    Set.range (((pushforward f).map (idealTorsionSubsheafι (I.pullback f) ℱ)).val.app (op U)) =
      Set.range ((idealTorsionSubsheafι I ((pushforward f).obj ℱ)).val.app (op U)))

end AlgebraicGeometry.AlgebraicSpace.Modules
