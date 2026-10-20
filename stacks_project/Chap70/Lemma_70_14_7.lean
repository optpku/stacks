/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.SectionsWithSupport.Pushforward
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace AlgebraicGeometry.AlgebraicSpace.Modules
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

/-
Lemma 70.14.7: let `S` be a scheme and `f : X ⟶ Y` a quasi-compact and quasi-separated
morphism of algebraic spaces over `S`. Let `T ⊂ |Y|` be a closed subset whose complement
corresponds to an open subspace `V ⊂ Y` with quasi-compact morphism `V ⟶ Y`. Let `F` be a
quasi-coherent `𝒪_X`-module, and let `F' ⊂ F` be the subsheaf of sections supported on
`|f|⁻¹ T`. Then `f_* F' ⊂ f_* F` is the subsheaf of sections supported on `T`. The complement
of `|f|⁻¹ T` is the support of the open subspace `U = f⁻¹ V ⊂ X`, presented by a cartesian
square over `V ⟶ Y`.
-/
@[stacks 085B]
#check (AlgebraicGeometry.AlgebraicSpace.Modules.range_pushforward_sectionsWithSupportInι_app_eq :
  ∀ {S : Scheme.{u}} {X Y U V : AlgebraicSpace S}
    (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    (ιV : V ⟶ Y) [IsOpenImmersion ιV] [QuasiCompact ιV]
    (ιU : U ⟶ X) [IsOpenImmersion ιU] (f' : U ⟶ V)
    (h_cart : IsPullback ιU f' f ιV)
    (F : X.Modules) [F.IsQuasicoherent] (W : smallEtaleSite Y),
    Set.range (((pushforward f).map (sectionsWithSupportInι ιU F)).val.app (op W)) =
      Set.range ((sectionsWithSupportInι ιV ((pushforward f).obj F)).val.app (op W)))

end AlgebraicGeometry.AlgebraicSpace.Modules
