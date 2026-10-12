/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap78.Definition_78_12_1_System

/-!
# Invertibility of the equivariance map

The equivariance map of a quasi-coherent module on a groupoid in algebraic spaces
is an isomorphism, with inverse obtained by reindexing along groupoid inversion.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidAlgebraicSpace.System

variable {S : Scheme.{u}} {B : AlgebraicSpace S}

/-- The inverse-oriented equivariance morphism obtained by reindexing the action along
groupoid inversion. -/
def actionInverse {G : GroupoidAlgebraicSpace B} (A : System G) :
    (AlgebraicSpace.QCoh.pullback G.s.left).obj A.obj ⟶
      (AlgebraicSpace.QCoh.pullback G.t.left).obj A.obj :=
  (pullbackEqIso (congrArg Over.Hom.left G.inverse_target)).inv.app A.obj ≫
    reindexAction G.t.left G.s.left G.i.left A.obj A.action ≫
      (pullbackEqIso (congrArg Over.Hom.left G.inverse_source)).hom.app A.obj

/-- The action followed by its inversion-induced inverse is the identity. -/
theorem action_comp_actionInverse {G : GroupoidAlgebraicSpace B} (A : System G) :
    A.action ≫ actionInverse A = 𝟙 _ := sorry

/-- The inversion-induced inverse followed by the action is the identity. -/
theorem actionInverse_comp_action {G : GroupoidAlgebraicSpace B} (A : System G) :
    actionInverse A ≫ A.action = 𝟙 _ := sorry

/-- The equivariance map bundled with its inverse induced by groupoid inversion. -/
def actionIso {G : GroupoidAlgebraicSpace B} (A : System G) :
    (AlgebraicSpace.QCoh.pullback G.t.left).obj A.obj ≅
      (AlgebraicSpace.QCoh.pullback G.s.left).obj A.obj where
  hom := A.action
  inv := actionInverse A
  hom_inv_id := action_comp_actionInverse A
  inv_hom_id := actionInverse_comp_action A

/-- The forward component of `actionIso` is the equivariance map. -/
theorem actionIso_hom {G : GroupoidAlgebraicSpace B} (A : System G) :
    (actionIso A).hom = A.action := sorry

/-- The action morphism of an equivariant quasi-coherent module is an isomorphism. -/
instance action_isIso {G : GroupoidAlgebraicSpace B} (A : System G) : IsIso A.action :=
  Iso.isIso_hom (actionIso A)

/-- The equivariance map of a quasi-coherent module on a groupoid is an isomorphism. -/
theorem action_isIso_of {G : GroupoidAlgebraicSpace B} {F : AlgebraicSpace.QCoh G.U.left}
    {α : (AlgebraicSpace.QCoh.pullback G.t.left).obj F ⟶
      (AlgebraicSpace.QCoh.pullback G.s.left).obj F}
    (h_cocycle : Cocycle G F α) (h_unit : Unit G F α) : IsIso α := sorry

end AlgebraicGeometry.GroupoidAlgebraicSpace.System
