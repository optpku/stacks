/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.VersalRing
public import ReasLib.AlgebraicGeometry.AlgebraicStack.FieldValuedPoint.Fiber
public import ReasLib.AlgebraicGeometry.CompleteLocalAlgebra.Hom
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Completion
public import ReasLib.AlgebraicGeometry.GroupoidsOver.SmoothFiniteTypeObject
public import ReasLib.RingTheory.Regular.GRing
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

open CategoryTheory AlgebraicGeometry IsLocalRing
open FiberedCategoryOver.Groupoids
open GroupoidsOver
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- A versal ring at a finite-type field-valued point of an algebraic stack
locally of finite type over a locally Noetherian scheme is the completed stalk
of a smooth finite-type scheme chart through that point, with the same residue
field, if the base stalk at its image is a G-ring. -/
@[stacks 0DR0]
theorem exists_smooth_of_isVersalRing {S : Scheme.{u}} [IsLocallyNoetherian S]
    {X : GroupoidsOver S} [AlgebraicStack X]
    [AlgebraicStack.LocallyOfFiniteType (baseProjection.{u + 1, u, u + 1} X)]
    (x0 : FieldValuedPoint X)
    [AlgebraicGeometry.LocallyOfFiniteType x0.structureHom]
    (A : CompleteLocalSAlgebra S) [IsVersalRing x0 A] (s : S)
    (hs : x0.structureHom (closedPoint x0.K) = s)
    [IsGRing (S.presheaf.stalk s)] :
    ∃ (W : SmoothFiniteTypeObject x0.structureHom x0.fiberObj)
      (φ : CompleteLocalSAlgebra.Hom A (completionSAlgebra W.toS W.u0)),
      Function.Bijective φ.hom :=
  sorry

end AlgebraicGeometry.AlgebraicStack
