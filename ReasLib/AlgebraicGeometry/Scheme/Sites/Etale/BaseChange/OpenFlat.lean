/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.ConnectedFiberOpens
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.BaseChange.Flat
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.FiniteOpenDecomposition

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme.Etale.BaseChange

variable {X Y S T : Scheme.{u}}

/-- Flat open morphisms with separably closed residue fields satisfy étale set-sheaf base change
under finite open decompositions and connected nonempty fibre-opens. -/
theorem setMap_isIso_of_openFlat_sepClosed (f : X ⟶ S) (h : Y ⟶ X) (e : Y ⟶ T) (g : T ⟶ S)
    [Flat f] (hf_open : IsOpenMap f.base) (h_cart : IsPullback h e f g)
    (h_res : ∀ s : S, IsSepClosed (S.residueField s))
    (h_split : HasFiniteOpenDecomposition X) (h_fib : Hom.HasConnectedFiberOpens f)
    (F : Sheaf T.smallEtaleTopology (Type (u + 1))) :
    IsIso (setMap f h e g h_cart F) := sorry

/-- Each component of the étale set-sheaf base-change comparison is invertible under the
same open-flat hypotheses. -/
theorem setMap_isIso_of_openFlat_sepClosed_app (f : X ⟶ S) (h : Y ⟶ X) (e : Y ⟶ T) (g : T ⟶ S)
    [Flat f] (hf_open : IsOpenMap f.base) (h_cart : IsPullback h e f g)
    (h_res : ∀ s : S, IsSepClosed (S.residueField s))
    (h_split : HasFiniteOpenDecomposition X) (h_fib : Hom.HasConnectedFiberOpens f)
    (F : Sheaf T.smallEtaleTopology (Type (u + 1))) (U : X.Etaleᵒᵖ) :
    IsIso ((setMap f h e g h_cart F).hom.app U) := sorry

end AlgebraicGeometry.Scheme.Etale.BaseChange
