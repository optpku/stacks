/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.BaseChange.SepClosed
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
open AlgebraicGeometry AlgebraicGeometry.Scheme

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

/- Lemma 59.87.3: for a cartesian square of schemes over the spectrum of a
separably closed field, the canonical set-valued étale base-change comparison
is an isomorphism. -/
@[stacks 0EZY] #check
  (AlgebraicGeometry.Scheme.Etale.BaseChange.setMap_isIso_of_isSepClosed :
    ∀ {k : Type u} [Field k] [IsSepClosed k] {X Y T : Scheme.{u}}
      (f : X ⟶ Spec (CommRingCat.of k)) (h : Y ⟶ X) (e : Y ⟶ T)
      (g : T ⟶ Spec (CommRingCat.of k)) (cart : IsPullback h e f g)
      (F : Sheaf T.smallEtaleTopology (Type (u + 1))),
      IsIso (AlgebraicGeometry.Scheme.Etale.BaseChange.setMap f h e g cart F))

/- Objectwise, the canonical set-valued étale base-change
comparison is an isomorphism on every object of `X_étale`. -/
#check
  (AlgebraicGeometry.Scheme.Etale.BaseChange.setMap_isIso_of_isSepClosed_app :
    ∀ {k : Type u} [Field k] [IsSepClosed k] {X Y T : Scheme.{u}}
      (f : X ⟶ Spec (CommRingCat.of k)) (h : Y ⟶ X) (e : Y ⟶ T)
      (g : T ⟶ Spec (CommRingCat.of k)) (cart : IsPullback h e f g)
      (F : Sheaf T.smallEtaleTopology (Type (u + 1))) (U : X.Etaleᵒᵖ),
      IsIso ((AlgebraicGeometry.Scheme.Etale.BaseChange.setMap f h e g cart F).hom.app U))

end AlgebraicGeometry.Scheme
