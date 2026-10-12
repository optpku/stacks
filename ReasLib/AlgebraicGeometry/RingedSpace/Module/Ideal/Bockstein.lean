/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Tensor.Exact
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Basic
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Ideal.Power.Quotient
public import ReasLib.CategoryTheory.DerivedCategory.Monoidal.Tensor
import Mathlib.Tactic.CrossRefAttribute

/-!
# The Bockstein complex of an invertible ideal sheaf

The short exact rows of successive ideal-power quotients give distinguished triangles after
tensoring with an arbitrary derived module.  Their homology connecting morphisms assemble into
the ideal Bockstein complex.  The construction depends only on the derived object, not on a
chosen cochain representative or on user-supplied exactness witnesses.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.Pretriangulated ComplexShape

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.IdealSheaf.Bockstein

variable {X : RingedSpace.{u}}

section

variable [∀ K L : CochainComplex X.Modules ℤ,
  HomologicalComplex.HasMapBifunctor K L (curriedTensor X.Modules) (up ℤ)]
variable [DerivedCategory.DerivedTensor.Left.Has (C := X.Modules)]

/-- The distinguished ideal-power quotient triangle after derived tensoring on the left by `M`. -/
noncomputable def triangle
    (I : Subobject (SheafOfModules.unit X.ringCatSheaf : X.Modules))
    [MonoidalCategory.isInvertibleObject (I : X.Modules)]
    (M : DerivedCategory X.Modules) (i : ℤ) :
    Triangle (DerivedCategory X.Modules) :=
  (DerivedCategory.DerivedTensor.Left.functor M).mapTriangle.obj
    (Power.row_shortExact I i).singleTriangle

/-- The derived ideal-power quotient triangle is distinguished. -/
theorem triangle_distinguished
    (I : Subobject (SheafOfModules.unit X.ringCatSheaf : X.Modules))
    [MonoidalCategory.isInvertibleObject (I : X.Modules)]
    (M : DerivedCategory X.Modules) (i : ℤ) :
    triangle I M i ∈ distTriang (DerivedCategory X.Modules) := sorry

/-- The degree-`i` Bockstein term
`H^i(M ⊗ᴸ (I^i / I^(i + 1))[0])`, using fixed-left derived tensoring. -/
noncomputable abbrev term
    (I : Subobject (SheafOfModules.unit X.ringCatSheaf : X.Modules))
    [MonoidalCategory.isInvertibleObject (I : X.Modules)]
    (M : DerivedCategory X.Modules) (i : ℤ) : X.Modules :=
  (DerivedCategory.homologyFunctor X.Modules i).obj
    ((DerivedCategory.DerivedTensor.Left.functor M).obj
      ((DerivedCategory.singleFunctor X.Modules 0).obj (Power.piece I i)))

/-- The Bockstein differential is the connecting morphism of the derived ideal-power quotient
triangle. -/
@[stacks 0GT8 "ideal-sheaf Bockstein differential"]
noncomputable def d
    (I : Subobject (SheafOfModules.unit X.ringCatSheaf : X.Modules))
    [MonoidalCategory.isInvertibleObject (I : X.Modules)]
    (M : DerivedCategory X.Modules) (i : ℤ) :
    term I M i ⟶ term I M (i + 1) :=
  DerivedCategory.HomologySequence.δ (triangle I M i) i (i + 1)

/-- Two consecutive ideal-sheaf Bockstein differentials compose to zero. -/
@[stacks 0GT8 "ideal-sheaf Bockstein differential squares to zero"]
theorem d_sq
    (I : Subobject (SheafOfModules.unit X.ringCatSheaf : X.Modules))
    [MonoidalCategory.isInvertibleObject (I : X.Modules)]
    (M : DerivedCategory X.Modules) (i : ℤ) :
    d I M i ≫ d I M (i + 1) = 0 := sorry

/-- The Bockstein cohomology complex `H^•(M / I)` attached canonically to a derived module. -/
@[stacks 0GT8 "ideal-sheaf Bockstein cohomology complex"]
noncomputable def complex
    (I : Subobject (SheafOfModules.unit X.ringCatSheaf : X.Modules))
    [MonoidalCategory.isInvertibleObject (I : X.Modules)]
    (M : DerivedCategory X.Modules) : CochainComplex X.Modules ℤ :=
  CochainComplex.of (term I M) (d I M) (d_sq I M)

/-- The degree-`i` object of the ideal-sheaf Bockstein complex. -/
@[simp, stacks 0GT8 "terms of the ideal-sheaf Bockstein complex"]
theorem complex_X
    (I : Subobject (SheafOfModules.unit X.ringCatSheaf : X.Modules))
    [MonoidalCategory.isInvertibleObject (I : X.Modules)]
    (M : DerivedCategory X.Modules) (i : ℤ) :
    (complex I M).X i = term I M i := sorry

/-- The differential of the ideal-sheaf Bockstein complex is its connecting morphism. -/
@[simp, stacks 0GT8 "differential of the ideal-sheaf Bockstein complex"]
theorem complex_d
    (I : Subobject (SheafOfModules.unit X.ringCatSheaf : X.Modules))
    [MonoidalCategory.isInvertibleObject (I : X.Modules)]
    (M : DerivedCategory X.Modules) (i : ℤ) :
    (complex I M).d i (i + 1) = d I M i := sorry

end

end AlgebraicGeometry.RingedSpace.IdealSheaf.Bockstein
