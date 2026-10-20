/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.Quasicoherent

/-!
# Inversion of equivariance maps

Groupoid inversion gives a reverse equivariance map whose composite with the
original action is the identity.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidAlgebraicSpace.QCoh

variable {S : Scheme.{u}} {B : AlgebraicSpace S}

/-- The inverse-oriented equivariance morphism obtained by reindexing the action along
groupoid inversion. -/
def actionInverse {G : GroupoidAlgebraicSpace B} (A : G.QCoh) :
    (AlgebraicSpace.QCoh.pullback G.s.left).obj A.obj ⟶
      (AlgebraicSpace.QCoh.pullback G.t.left).obj A.obj :=
  (pullbackEqIso (congrArg Over.Hom.left G.inverse_target)).inv.app A.obj ≫
    reindexAction G.t.left G.s.left G.i.left A.obj A.action ≫
      (pullbackEqIso (congrArg Over.Hom.left G.inverse_source)).hom.app A.obj

/-- The inversion-induced inverse followed by the action is the identity. -/
theorem actionInverse_comp_action {G : GroupoidAlgebraicSpace B} (A : G.QCoh) :
    actionInverse A ≫ A.action = 𝟙 _ := sorry

/-- The action followed by its inversion-induced inverse is the identity. -/
theorem action_comp_actionInverse {G : GroupoidAlgebraicSpace B} (A : G.QCoh) :
    A.action ≫ actionInverse A = 𝟙 _ := sorry

/-- The equivariance map bundled with its inverse induced by groupoid inversion. -/
def actionIso {G : GroupoidAlgebraicSpace B} (A : G.QCoh) :
    (AlgebraicSpace.QCoh.pullback G.t.left).obj A.obj ≅
      (AlgebraicSpace.QCoh.pullback G.s.left).obj A.obj where
  hom := A.action
  inv := actionInverse A
  hom_inv_id := action_comp_actionInverse A
  inv_hom_id := actionInverse_comp_action A

/-- The forward component of the action isomorphism is the equivariance map. -/
theorem actionIso_hom {G : GroupoidAlgebraicSpace B} (A : G.QCoh) :
    (actionIso A).hom = A.action := rfl

/-- The action morphism of an equivariant quasi-coherent module is an isomorphism. -/
theorem action_isIso {G : GroupoidAlgebraicSpace B} (A : G.QCoh) : IsIso A.action :=
  Iso.isIso_hom (actionIso A)

end AlgebraicGeometry.GroupoidAlgebraicSpace.QCoh
