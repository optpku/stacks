module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FunctorOfPoints
public import Mathlib.CategoryTheory.CommSq
public import Mathlib.CategoryTheory.Comma.Over.Basic

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- A bundled factorization of `f ≫ π` through an intermediate algebraic space. -/
abbrev FiniteTypeApproximationDiagram {S : Scheme.{u}} {X B Bi : AlgebraicSpace S}
    (f : X ⟶ B) (π : B ⟶ Bi) :=
  Under (Over.mk (f ≫ π) : Over Bi)

namespace FiniteTypeApproximationDiagram

variable {S : Scheme.{u}} {X B Bi : AlgebraicSpace S} {f : X ⟶ B} {π : B ⟶ Bi}

/-- Construct a bundled factorization from a commuting square of algebraic spaces. -/
abbrev mk (W : AlgebraicSpace S) (toW : X ⟶ W) (toBi : W ⟶ Bi)
    (comm : CommSq toW f toBi π) :
    FiniteTypeApproximationDiagram f π :=
  Under.mk
    (Over.homMk toW comm.w :
      (Over.mk (f ≫ π) : Over Bi) ⟶ Over.mk toBi)

/-- The intermediate algebraic space in a finite-type approximation diagram. -/
abbrev W (D : FiniteTypeApproximationDiagram f π) : AlgebraicSpace S :=
  D.right.left

/-- The morphism from the source to the intermediate algebraic space. -/
abbrev toW (D : FiniteTypeApproximationDiagram f π) : X ⟶ D.W :=
  D.hom.left

/-- The morphism from the intermediate algebraic space to the stage algebraic space. -/
abbrev toBi (D : FiniteTypeApproximationDiagram f π) : D.W ⟶ Bi :=
  D.right.hom

/-- The morphisms in a finite-type approximation diagram form a commuting square. -/
abbrev comm (D : FiniteTypeApproximationDiagram f π) :
    CommSq D.toW f D.toBi π :=
  CommSq.mk D.hom.w

/-- The intermediate algebraic space of a diagram constructed by `mk` is the supplied space. -/
theorem mk_W (W : AlgebraicSpace S) (toW : X ⟶ W) (toBi : W ⟶ Bi)
    (comm : CommSq toW f toBi π) :
    (mk W toW toBi comm).W = W :=
  sorry

/-- The top morphism of a diagram constructed by `mk` is the supplied morphism. -/
theorem mk_toW (W : AlgebraicSpace S) (toW : X ⟶ W) (toBi : W ⟶ Bi)
    (comm : CommSq toW f toBi π) :
    (mk W toW toBi comm).toW = toW :=
  sorry

/-- The right morphism of a diagram constructed by `mk` is the supplied morphism. -/
theorem mk_toBi (W : AlgebraicSpace S) (toW : X ⟶ W) (toBi : W ⟶ Bi)
    (comm : CommSq toW f toBi π) :
    (mk W toW toBi comm).toBi = toBi :=
  sorry

/-- The commuting square of a diagram constructed by `mk` is the supplied square. -/
theorem mk_comm (W : AlgebraicSpace S) (toW : X ⟶ W) (toBi : W ⟶ Bi)
    (comm : CommSq toW f toBi π) :
    (mk W toW toBi comm).comm = comm :=
  sorry

/-- The composite through the intermediate algebraic space equals the prescribed composite. -/
theorem w (D : FiniteTypeApproximationDiagram f π) :
    D.toW ≫ D.toBi = f ≫ π :=
  sorry

end FiniteTypeApproximationDiagram

end AlgebraicGeometry.AlgebraicSpace
