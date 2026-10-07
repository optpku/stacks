module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Complex.Monoidal
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Basic
public import ReasLib.CategoryTheory.DerivedCategory.Monoidal.Tensor
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Derived tensor product on a ringed space

This is the ringed-space source-facing facade for the canonical fixed-right derived tensor owner.
The underlying data are `DerivedTensor.Right.functor` and its counit; no chosen representative or
chapter-local quotient lift is introduced here.
-/

open AlgebraicGeometry CategoryTheory ComplexShape

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

variable {X : RingedSpace.{u}}

/-- Fixed-right unbounded derived tensor products exist for modules on a ringed space. -/
instance hasDerivedTensorRight (X : RingedSpace.{u}) :
    DerivedCategory.DerivedTensor.Right.Has (C := Modules X) := sorry

/-- The fixed-right source functor on a chosen cochain-complex representative. -/
@[stacks 06YH "ringed-space fixed-right source on complexes"]
noncomputable abbrev derivedTensorSourceHomotopyFunctorOfComplex
    (K : CochainComplex (Modules X) ℤ) :
    HomotopyCategory (Modules X) (up ℤ) ⥤ ModuleDerived X :=
  DerivedCategory.DerivedTensor.Right.sourceFunctorOfComplex K

/-- The fixed-right source functor on the homotopy category. -/
@[stacks 06YH "ringed-space fixed-right source"]
noncomputable abbrev derivedTensorSourceFunctor (L : ModuleDerived X) :
    HomotopyCategory (Modules X) (up ℤ) ⥤ ModuleDerived X :=
  DerivedCategory.DerivedTensor.Right.sourceFunctor L

/-- The canonical fixed-right derived tensor endofunctor. -/
@[stacks 06YH "ringed-space fixed-right derived tensor owner"]
noncomputable abbrev derivedTensorProduct (L : ModuleDerived X) :
    ModuleDerived X ⥤ ModuleDerived X :=
  DerivedCategory.DerivedTensor.Right.functor L

/-- The canonical counit of the fixed-right derived tensor functor. -/
@[stacks 06YH "ringed-space fixed-right derived tensor counit"]
noncomputable abbrev derivedTensorProductCounit (L : ModuleDerived X) :
    DerivedCategory.Qh ⋙ derivedTensorProduct L ⟶ derivedTensorSourceFunctor L :=
  DerivedCategory.DerivedTensor.Right.counit L

/-- The fixed-right source functor has the left-derived universal property. -/
@[stacks 06YH "ringed-space fixed-right source derivability"]
theorem derivedTensorSourceFunctor_hasLeftDerivedFunctor (L : ModuleDerived X) :
    (derivedTensorSourceFunctor L).HasLeftDerivedFunctor
      (HomotopyCategory.quasiIso (Modules X) (up ℤ)) := sorry

/-- The canonical fixed-right derived tensor functor is a left-derived functor of its source. -/
@[stacks 06YH "ringed-space fixed-right derived tensor derivability"]
theorem derivedTensorProduct_isLeftDerivedFunctor (L : ModuleDerived X) :
    (derivedTensorProduct L).IsLeftDerivedFunctor
      (derivedTensorProductCounit L)
      (HomotopyCategory.quasiIso (Modules X) (up ℤ)) := sorry

/-- Fixed-right derived tensoring commutes with integer shifts. -/
@[stacks 06YH "ringed-space fixed-right derived tensor shift"]
noncomputable abbrev derivedTensorProduct_commShift (L : ModuleDerived X) :
    (derivedTensorProduct L).CommShift ℤ :=
  DerivedCategory.DerivedTensor.Right.commShift L

/-- Fixed-right derived tensoring is triangulated exact. -/
@[stacks 06YH "ringed-space fixed-right derived tensor triangulated"]
theorem derivedTensorProduct_isTriangulated (L : ModuleDerived X) :
    (derivedTensorProduct L).IsTriangulated := sorry

attribute [instance] derivedTensorSourceFunctor_hasLeftDerivedFunctor
attribute [instance] derivedTensorProduct_isLeftDerivedFunctor
attribute [instance] derivedTensorProduct_isTriangulated

end AlgebraicGeometry.RingedSpace

namespace AlgebraicGeometry.RingedSpace.ModuleDerived.Tensor

/-! Short names for the canonical fixed-right source layer.  The longer ringed-space names above
are retained as source-compatible bridges; new code can stay inside this namespace. -/

/-- The fixed-right source functor on a cochain-complex representative. -/
@[stacks 06YH "short fixed-right source on complexes"]
noncomputable abbrev sourceOfComplex
    {X : RingedSpace.{u}} (K : CochainComplex (Modules X) ℤ) :
    HomotopyCategory (Modules X) (up ℤ) ⥤ ModuleDerived X :=
  AlgebraicGeometry.RingedSpace.derivedTensorSourceHomotopyFunctorOfComplex K

/-- The fixed-right source functor on the homotopy category. -/
@[stacks 06YH "short fixed-right source"]
noncomputable abbrev source {X : RingedSpace.{u}} (L : ModuleDerived X) :
    HomotopyCategory (Modules X) (up ℤ) ⥤ ModuleDerived X :=
  AlgebraicGeometry.RingedSpace.derivedTensorSourceFunctor L

end AlgebraicGeometry.RingedSpace.ModuleDerived.Tensor

namespace RingedTensor

/- Scoped source-facing notation for the ringed-space derived tensor object. -/
set_option quotPrecheck false in
scoped notation:70 K:70 " ⊗^L " L:71 =>
  (AlgebraicGeometry.RingedSpace.derivedTensorProduct L).obj K

end RingedTensor

end
