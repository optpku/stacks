/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
public import Mathlib.CategoryTheory.Localization.Linear
public import ReasLib.Algebra.Category.DifferentialGraded.Functor.Homotopy
public import ReasLib.Algebra.Homology.DifferentialGradedModule.Bimodule.InternalHom.Triangulated
public import ReasLib.Algebra.Homology.DifferentialGradedModule.Derived
public import ReasLib.CategoryTheory.Functor.Derived.Total.Triangulated
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Derived Internal Hom from a Differential Graded Bimodule

This file owns the total right-derived functor of the concrete fixed-source internal-Hom DG
functor.  It is the right-derived counterpart of `DifferentialGradedBimodule.Tensor.derivedFunctor`.
-/

@[expose] public section

noncomputable section

universe u v w x

open CategoryTheory
open DifferentialGradedCategory
open scoped DifferentialGradedCategory

namespace DifferentialGradedBimodule.InternalHom

variable {R : Type u} [CommRing R]
variable {A : CochainDGAlgebra.{u, w} R} {B : CochainDGAlgebra.{u, x} R}

/-- Fixed-source internal Hom followed by the canonical localization of right DG `A`-modules.
This is the homotopy-level source whose total right-derived functor is `derivedFunctor T`. -/
@[stacks 09LI "homotopy-level source of derived internal Hom"]
abbrev derivedSourceFunctor (T : DifferentialGradedBimodule.{u, v, w, x} A B) :
    K R (DifferentialGradedModule.{u, v} B) ⥤
      DifferentialGradedModule.Derived.Category.{u, v} A :=
  (internalHomDgFunctor T).mapK ⋙ DifferentialGradedModule.Derived.Q A

/-- Fixed-source internal Hom from `T` has a source-defined right-derived value at every object.
This reusable owner supplies Mathlib's pointwise and total right-derived-functor predicates. -/
@[stacks 09LI "definedness predicate for derived internal Hom"]
abbrev HasDerivedFunctor (T : DifferentialGradedBimodule.{u, v, w, x} A B) : Prop :=
  Functor.RightDerived.EverywhereDefined (derivedSourceFunctor T)
    (DifferentialGradedModule.quasiIso B)

/-- Property-(I) resolutions give fixed-source internal Hom a canonical total right-derived
functor for every differential graded bimodule. -/
@[stacks 09LI "property-I definedness of derived internal Hom"]
instance hasDerivedFunctor (T : DifferentialGradedBimodule.{u, v, w, x} A B) :
    HasDerivedFunctor T := sorry

/-- Fixed-source internal Hom has a total right-derived functor in Mathlib's canonical sense.
This direct endpoint keeps downstream typeclass search from unfolding the pointwise-definedness
bridge each time it constructs the total derived functor. -/
@[stacks 09LI "existence of total derived internal Hom"]
instance hasRightDerivedFunctor (T : DifferentialGradedBimodule.{u, v, w, x} A B) :
    (derivedSourceFunctor T).HasRightDerivedFunctor
      (DifferentialGradedModule.quasiIso B) := sorry

/-- The total right-derived fixed-source internal-Hom functor. -/
@[stacks 09LI "derived internal Hom functor of a differential graded bimodule",
  stacks 0FTP "derived internal Hom"]
noncomputable def derivedFunctor (T : DifferentialGradedBimodule.{u, v, w, x} A B) :
    DifferentialGradedModule.Derived.Category.{u, v} B ⥤
      DifferentialGradedModule.Derived.Category.{u, v} A :=
  (derivedSourceFunctor T).totalRightDerived
    (DifferentialGradedModule.Derived.Q B)
    (DifferentialGradedModule.quasiIso B)

/-- The canonical comparison from underived internal Hom on the homotopy category to its total
right-derived functor. -/
@[stacks 0FTP "unit of derived internal Hom"]
noncomputable def derivedUnit (T : DifferentialGradedBimodule.{u, v, w, x} A B) :
    derivedSourceFunctor T ⟶
      DifferentialGradedModule.Derived.Q B ⋙ derivedFunctor T :=
  (derivedSourceFunctor T).totalRightDerivedUnit
    (DifferentialGradedModule.Derived.Q B)
    (DifferentialGradedModule.quasiIso B)

/-- Derived fixed-source internal Hom is `R`-linear. -/
@[stacks 09LI "linearity of derived internal Hom"]
instance derivedFunctor_linear (T : DifferentialGradedBimodule.{u, v, w, x} A B) :
    (derivedFunctor T).Linear R := sorry

/-- Derived fixed-source internal Hom commutes with integer shifts. -/
@[stacks 09LI "shift compatibility of derived internal Hom"]
noncomputable instance derivedFunctor_commShift (T : DifferentialGradedBimodule.{u, v, w, x} A B) :
    (derivedFunctor T).CommShift ℤ :=
  Functor.totalRightDerived_commShift (derivedSourceFunctor T)
    (DifferentialGradedModule.quasiIso B)
    (DifferentialGradedModule.Derived.Q B)

/-- Derived fixed-source internal Hom is triangulated. -/
@[stacks 09LI "triangulated derived internal Hom"]
instance derivedFunctor_isTriangulated (T : DifferentialGradedBimodule.{u, v, w, x} A B) :
    (derivedFunctor T).IsTriangulated := sorry

/-- `derivedFunctor T` with its canonical unit satisfies the universal property of the total
right-derived internal-Hom functor. -/
@[stacks 09LI "universal property of derived internal Hom"]
instance derivedFunctor_isRightDerived (T : DifferentialGradedBimodule.{u, v, w, x} A B) :
    (derivedFunctor T).IsRightDerivedFunctor (derivedUnit T)
      (DifferentialGradedModule.quasiIso B) := sorry

end DifferentialGradedBimodule.InternalHom
