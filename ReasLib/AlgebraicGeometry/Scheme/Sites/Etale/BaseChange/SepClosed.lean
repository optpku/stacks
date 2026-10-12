/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.BaseChange.Set
public import Mathlib.FieldTheory.IsSepClosed

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
open AlgebraicGeometry AlgebraicGeometry.Scheme

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale.BaseChange

variable {k : Type u} [Field k] [IsSepClosed k]
variable {X Y T : Scheme.{u}}

/-- For a cartesian square of schemes over the spectrum of a separably closed
field, the canonical set-valued étale base-change comparison is an isomorphism. -/
@[instance]
theorem setMap_isIso_of_isSepClosed
    (f : X ⟶ Spec (CommRingCat.of k)) (h : Y ⟶ X) (e : Y ⟶ T)
    (g : T ⟶ Spec (CommRingCat.of k)) (cart : IsPullback h e f g)
    (F : Sheaf T.smallEtaleTopology (Type (u + 1))) :
    IsIso (setMap f h e g cart F) := sorry

/-- For every object of the étale site of `X`, the component of the canonical
set-valued étale base-change comparison is an isomorphism. -/
theorem setMap_isIso_of_isSepClosed_app
    (f : X ⟶ Spec (CommRingCat.of k)) (h : Y ⟶ X) (e : Y ⟶ T)
    (g : T ⟶ Spec (CommRingCat.of k)) (cart : IsPullback h e f g)
    (F : Sheaf T.smallEtaleTopology (Type (u + 1))) (U : X.Etaleᵒᵖ) :
    IsIso ((setMap f h e g cart F).hom.app U) := sorry

end AlgebraicGeometry.Scheme.Etale.BaseChange

end
