/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Presheaf.Fiber
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points.Topology

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits Opposite
open CategoryTheory.ObjectProperty TopologicalSpace TypeCat
open AlgebraicGeometry.AlgebraicSpace AlgebraicGeometry.Scheme.Over

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The algebraic space over `V` whose `T`-points are maps into `X` over `V`. -/
def sliceSpace {S : Scheme.{u}} {V : Over S} (X : AlgebraicSpace S)
    (f : X ⟶ ofOver V) : AlgebraicSpace V.left :=
  ofFunctor (Scheme.Over.fiberFunctor f (yonedaEquiv (𝟙 (ofOver V)))) sorry sorry sorry

/-- The functor of points of `sliceSpace X f` is `Scheme.Over.fiberFunctor f (yonedaEquiv (𝟙 (ofOver V)))`. -/
theorem sliceSpace_functorOfPoints {S : Scheme.{u}} {V : Over S}
    (X : AlgebraicSpace S) (f : X ⟶ ofOver V) :
    (sliceSpace X f).functorOfPoints = Scheme.Over.fiberFunctor f (yonedaEquiv (𝟙 (ofOver V))) :=
  rfl

/-- A field-valued point of `sliceSpace X f` determines a field-valued point of
`X` by composing the structure morphism with `V ⟶ S`. -/
def fieldValuedPoint_sliceSpace {S : Scheme.{u}} {V : Over S}
    {X : AlgebraicSpace S} (f : X ⟶ ofOver V)
    (p : FieldValuedPoint (sliceSpace X f)) : FieldValuedPoint X :=
  FieldValuedPoint.of p.K (p.structureHom ≫ V.hom) (yonedaEquiv.symm (p.elem).1)

/-- Equivalence of field-valued points is preserved by `fieldValuedPoint_sliceSpace`. -/
theorem equivalent_fieldValuedPoint_sliceSpace {S : Scheme.{u}} {V : Over S}
    {X : AlgebraicSpace S} (f : X ⟶ ofOver V)
    {p q : FieldValuedPoint (sliceSpace X f)}
    (h : FieldValuedPoint.Equivalent p q) :
    FieldValuedPoint.Equivalent (fieldValuedPoint_sliceSpace f p)
      (fieldValuedPoint_sliceSpace f q) :=
  sorry

/-- The map on points from the slice of `X` over `V` to `X`. -/
def pointsSlice {S : Scheme.{u}} {V : Over S} (X : AlgebraicSpace S)
    (f : X ⟶ ofOver V) : Points (sliceSpace X f) → Points X :=
  Quotient.map (fieldValuedPoint_sliceSpace f)
    fun _ _ h ↦ equivalent_fieldValuedPoint_sliceSpace f h

/-- `pointsSlice X f` is continuous. -/
theorem continuous_pointsSlice {S : Scheme.{u}} {V : Over S}
    (X : AlgebraicSpace S) (f : X ⟶ ofOver V) :
    Continuous (pointsSlice X f) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
