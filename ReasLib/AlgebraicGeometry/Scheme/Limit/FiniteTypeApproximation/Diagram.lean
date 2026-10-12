/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.CategoryTheory.CommSq
public import Mathlib.CategoryTheory.Comma.Over.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Limit.BaseChange

@[expose] public section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry

/-- A bundled factorization of `f ≫ π` through an intermediate scheme. -/
abbrev FiniteTypeApproximationDiagram {X S Si : Scheme.{u}}
    (f : X ⟶ S) (π : S ⟶ Si) :=
  Under (Over.mk (f ≫ π) : Over Si)

namespace FiniteTypeApproximationDiagram

variable {X S Si : Scheme.{u}} {f : X ⟶ S} {π : S ⟶ Si}

/-- Construct a bundled factorization from a commuting square of schemes. -/
abbrev mk (W : Scheme.{u}) (toW : X ⟶ W) (toSi : W ⟶ Si)
    (comm : CommSq toW f toSi π) :
    FiniteTypeApproximationDiagram f π :=
  Under.mk
    (Over.homMk toW comm.w :
      (Over.mk (f ≫ π) : Over Si) ⟶ Over.mk toSi)

/-- The intermediate scheme in a finite-type approximation diagram. -/
abbrev W (D : FiniteTypeApproximationDiagram f π) : Scheme.{u} :=
  D.right.left

/-- The morphism from the source to the intermediate scheme. -/
abbrev toW (D : FiniteTypeApproximationDiagram f π) : X ⟶ D.W :=
  D.hom.left

/-- The morphism from the intermediate scheme to the target scheme. -/
abbrev toSi (D : FiniteTypeApproximationDiagram f π) : D.W ⟶ Si :=
  D.right.hom

/-- The morphisms in a finite-type approximation diagram form a commuting square. -/
abbrev comm (D : FiniteTypeApproximationDiagram f π) :
    CommSq D.toW f D.toSi π :=
  CommSq.mk D.hom.w

/-- The intermediate scheme of a diagram constructed by `mk` is the supplied scheme. -/
@[simp] theorem mk_W (W : Scheme.{u}) (toW : X ⟶ W) (toSi : W ⟶ Si)
    (comm : CommSq toW f toSi π) :
    (mk W toW toSi comm).W = W :=
  rfl

/-- The top morphism of a diagram constructed by `mk` is the supplied morphism. -/
@[simp] theorem mk_toW (W : Scheme.{u}) (toW : X ⟶ W) (toSi : W ⟶ Si)
    (comm : CommSq toW f toSi π) :
    (mk W toW toSi comm).toW = toW :=
  rfl

/-- The right morphism of a diagram constructed by `mk` is the supplied morphism. -/
@[simp] theorem mk_toSi (W : Scheme.{u}) (toW : X ⟶ W) (toSi : W ⟶ Si)
    (comm : CommSq toW f toSi π) :
    (mk W toW toSi comm).toSi = toSi :=
  rfl

/-- The commuting square of a diagram constructed by `mk` is the supplied square. -/
@[simp] theorem mk_comm (W : Scheme.{u}) (toW : X ⟶ W) (toSi : W ⟶ Si)
    (comm : CommSq toW f toSi π) :
    (mk W toW toSi comm).comm = comm := by
  cases comm
  rfl

/-- The composite through the intermediate scheme equals the prescribed composite. -/
@[simp] theorem w (D : FiniteTypeApproximationDiagram f π) :
    D.toW ≫ D.toSi = f ≫ π :=
  D.comm.w

/-- The canonical cone from the source scheme to the stagewise base changes determined by a
finite-type approximation diagram. -/
noncomputable def baseChangeCone {I : Type u} [Preorder I]
    (D : OrderDual I ⥤ Scheme.{u}) (c : Cone D) {i : I}
    {X : Scheme.{u}} {f : X ⟶ c.pt}
    (approximation : FiniteTypeApproximationDiagram f (c.π.app i)) :
    Cone (Scheme.baseChangeOverDiagram D (show OrderDual I from i) approximation.toSi) :=
  (Scheme.baseChangeOverCone D c (show OrderDual I from i) approximation.toSi).extend
    (pullback.lift f approximation.toW approximation.w.symm)

end FiniteTypeApproximationDiagram

end AlgebraicGeometry
