module

public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
public import Mathlib.CategoryTheory.Localization.Linear
public import ReasLib.Algebra.Category.DifferentialGraded.Functor.Homotopy
public import ReasLib.Algebra.Homology.DifferentialGradedModule.Bimodule.TensorProduct.Triangulated
public import ReasLib.Algebra.Homology.DifferentialGradedModule.Derived
public import ReasLib.CategoryTheory.Functor.Derived.Total.Triangulated
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Derived Tensoring by a Differential Graded Bimodule

This file derives the concrete relative-tensor DG functor.  The source functor and its
derivability hypothesis are named separately, so results about resolutions can provide the
standard `HasLeftDerivedFunctor` instance without choosing a second notion of derived tensor.
-/

@[expose] public section

noncomputable section

universe u v w x y

open CategoryTheory
open DifferentialGradedCategory
open scoped DifferentialGradedCategory

namespace DifferentialGradedBimodule.Tensor

variable {R : Type u} [CommRing R]
variable {A : CochainDGAlgebra.{u, x} R} {B : CochainDGAlgebra.{u, y} R}

/-- Tensoring by `N`, followed by the canonical localization of right DG `B`-modules.  This is
the homotopy-level source whose total left derived functor is `derivedFunctor N`. -/
@[stacks 09LS "homotopy-level source of derived tensor"]
abbrev derivedSourceFunctor (N : DifferentialGradedBimodule.{u, w, x, y} A B) :
    K R (DifferentialGradedModule.{u, v} A) ⥤
      DifferentialGradedModule.Derived.Category.{u, max v w} B :=
  (dgFunctor N).mapK ⋙ DifferentialGradedModule.Derived.Q B

/-- Tensoring by a fixed DG bimodule has a source-defined left-derived value at every object.

This compatibility predicate has an independent source-module universe, so callers without an
expected functor type should supply all universe arguments.  New APIs should normally state the
canonical predicate directly on `derivedSourceFunctor`, which carries that universe in its type.
-/
@[stacks 09LS "definedness predicate for derived tensor"]
abbrev HasDerivedFunctor (N : DifferentialGradedBimodule.{u, w, x, y} A B) : Prop :=
  Functor.LeftDerived.EverywhereDefined
    (derivedSourceFunctor.{u, v, w, x, y} N)
    (DifferentialGradedModule.quasiIso.{u, v, x} A)

/-- Property-(P) resolutions give the tensor source functor a canonical total left-derived
functor for every differential graded bimodule. -/
@[stacks 09LS "property-P definedness of derived tensor"]
instance hasDerivedFunctor (N : DifferentialGradedBimodule.{u, w, x, y} A B) :
    HasDerivedFunctor.{u, v, w, x, y} N := sorry

/-- Tensoring by a fixed DG bimodule has a total left-derived functor in Mathlib's canonical
sense. This direct endpoint keeps downstream typeclass search from unfolding the
pointwise-definedness bridge each time it constructs the total derived functor. -/
@[stacks 09LS "existence of total derived tensor"]
instance hasLeftDerivedFunctor (N : DifferentialGradedBimodule.{u, w, x, y} A B) :
    (derivedSourceFunctor.{u, v, w, x, y} N).HasLeftDerivedFunctor
      (DifferentialGradedModule.quasiIso.{u, v, x} A) := sorry

/-- The total left derived functor of tensoring by a fixed differential graded bimodule. -/
@[stacks 09LS "derived tensor functor of a differential graded bimodule",
  stacks 0FTG "derived tensor product"]
noncomputable def derivedFunctor (N : DifferentialGradedBimodule.{u, w, x, y} A B)
    : DifferentialGradedModule.Derived.Category.{u, v} A ⥤
      DifferentialGradedModule.Derived.Category.{u, max v w} B :=
  (derivedSourceFunctor.{u, v, w, x, y} N).totalLeftDerived
    (DifferentialGradedModule.Derived.Q.{u, v, x} A)
    (DifferentialGradedModule.quasiIso.{u, v, x} A)

/-- The canonical comparison from derived tensoring to underived tensoring on the homotopy
category. -/
@[stacks 09LS "derived tensor counit"]
noncomputable def derivedCounit (N : DifferentialGradedBimodule.{u, w, x, y} A B)
    : DifferentialGradedModule.Derived.Q.{u, v, x} A ⋙ derivedFunctor N ⟶
      derivedSourceFunctor.{u, v, w, x, y} N :=
  (derivedSourceFunctor.{u, v, w, x, y} N).totalLeftDerivedCounit
    (DifferentialGradedModule.Derived.Q.{u, v, x} A)
    (DifferentialGradedModule.quasiIso.{u, v, x} A)

/-- Derived tensoring by a DG bimodule is `R`-linear. -/
@[stacks 09LS "linearity of derived tensor"]
instance derivedFunctor_linear (N : DifferentialGradedBimodule.{u, w, x, y} A B) :
    (derivedFunctor N).Linear R := sorry

/-- Derived tensoring by a DG bimodule commutes with integer shifts. -/
@[stacks 09LS "shift compatibility of derived tensor"]
noncomputable instance derivedFunctor_commShift
    (N : DifferentialGradedBimodule.{u, w, x, y} A B) :
    (derivedFunctor N).CommShift ℤ :=
  Functor.totalLeftDerived_commShift (derivedSourceFunctor.{u, v, w, x, y} N)
    (DifferentialGradedModule.quasiIso.{u, v, x} A)
    (DifferentialGradedModule.Derived.Q.{u, v, x} A)

/-- Derived tensoring by a DG bimodule is triangulated. -/
@[stacks 09LS "triangulated derived tensor"]
instance derivedFunctor_isTriangulated
    (N : DifferentialGradedBimodule.{u, w, x, y} A B) :
    (derivedFunctor N).IsTriangulated := sorry

/-- `derivedFunctor N` with its canonical counit satisfies the universal property of the total
left derived tensor functor. -/
@[stacks 09LS "universal property of derived tensor"]
instance derivedFunctor_isLeftDerived
    (N : DifferentialGradedBimodule.{u, w, x, y} A B) :
    (derivedFunctor N).IsLeftDerivedFunctor (derivedCounit N)
      (DifferentialGradedModule.quasiIso.{u, v, x} A) := sorry

section

variable (N : DifferentialGradedBimodule.{u, w, x, y} A B)

#synth HasDerivedFunctor.{u, v, w, x, y} N
#synth (derivedSourceFunctor.{u, v, w, x, y} N).HasLeftDerivedFunctor
  (DifferentialGradedModule.quasiIso.{u, v, x} A)
#synth (derivedFunctor.{u, v, w, x, y} N).CommShift ℤ
#synth (derivedFunctor.{u, v, w, x, y} N).IsTriangulated

end

end DifferentialGradedBimodule.Tensor
