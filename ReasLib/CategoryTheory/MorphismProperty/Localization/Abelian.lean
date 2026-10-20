module

public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.MorphismProperty.Localization.FiniteShapes
public import ReasLib.CategoryTheory.MorphismProperty.Localization.Preadditive

/-!
# Abelian Localizations

Let `W` be a morphism property on an abelian category.  A left calculus of fractions gives
cokernels in `W.Localization`, a right calculus gives kernels, and the two structures together
make the localization abelian.  The preservation half is inherited from the finite-shape
localization API.
-/

@[expose] public section

open CategoryTheory.Limits

universe v u

namespace CategoryTheory

open MorphismProperty

namespace MorphismProperty.Localization

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- A left-fraction localization of an abelian category has cokernels. -/
@[stacks 05QG "left-fraction localizations have cokernels"]
noncomputable instance instHasCokernelsOfHasLeftCalculusOfFractions
    (W : MorphismProperty C) [W.HasLeftCalculusOfFractions] :
    HasCokernels W.Localization := sorry

/-- The canonical left-fraction localization functor preserves the cokernel of every morphism. -/
theorem Q_preservesCokernel (W : MorphismProperty C) [W.HasLeftCalculusOfFractions]
    {X Y : C} (f : X ⟶ Y) : PreservesColimit (parallelPair f 0) W.Q := sorry

/-- A right-fraction localization of an abelian category has kernels. -/
@[stacks 05QG "right-fraction localizations have kernels"]
noncomputable instance instHasKernelsOfHasRightCalculusOfFractions
    (W : MorphismProperty C) [W.HasRightCalculusOfFractions] :
    HasKernels W.Localization := sorry

/-- The canonical right-fraction localization functor preserves the kernel of every morphism. -/
theorem Q_preservesKernel (W : MorphismProperty C) [W.HasRightCalculusOfFractions]
    {X Y : C} (f : X ⟶ Y) : PreservesLimit (parallelPair f 0) W.Q := sorry

/-- Under both calculi, the kernel structure is expressed using the canonical left-fraction
preadditive structure selected by instance priority. -/
noncomputable instance (priority := 110) instHasKernelsOfCalculusOfFractions
    (W : MorphismProperty C) [W.HasLeftCalculusOfFractions]
    [W.HasRightCalculusOfFractions] :
    HasKernels W.Localization := sorry

/-- The coimage-image comparison of every morphism in an abelian localization is invertible. -/
instance instIsIsoCoimageImageComparison
    (W : MorphismProperty C) [W.HasLeftCalculusOfFractions]
    [W.HasRightCalculusOfFractions] {X Y : W.Localization}
    (f : X ⟶ Y) : IsIso (Abelian.coimageImageComparison f) := sorry

/-- A localization by a two-sided calculus of fractions of an abelian category is abelian. -/
@[stacks 05QG "two-sided localizations of abelian categories are abelian"]
noncomputable instance instAbelian
    (W : MorphismProperty C) [W.HasLeftCalculusOfFractions]
    [W.HasRightCalculusOfFractions] : Abelian W.Localization :=
  Abelian.ofCoimageImageComparisonIsIso

/-- The canonical functor to an abelian localization is exact. -/
@[stacks 05QG "the localization functor is exact"]
theorem Q_exact (W : MorphismProperty C) [W.HasLeftCalculusOfFractions]
    [W.HasRightCalculusOfFractions] : exactFunctor C W.Localization W.Q := sorry

end MorphismProperty.Localization

end CategoryTheory
