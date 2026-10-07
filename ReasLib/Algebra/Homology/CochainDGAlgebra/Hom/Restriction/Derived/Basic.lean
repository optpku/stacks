module

public import ReasLib.Algebra.Homology.CochainDGAlgebra.Hom.Restriction
public import ReasLib.Algebra.Homology.DifferentialGradedModule.Derived
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Derived Restriction of Scalars

Restriction of scalars preserves quasi-isomorphisms, hence descends canonically through the
Verdier localizations of differential graded modules.  This leaf owns only that localization
lift and its factorization.
-/

@[expose] public section

noncomputable section

universe u v w x

open CategoryTheory DifferentialGradedCategory
open scoped DifferentialGradedCategory DifferentialGradedModule

namespace CochainDGAlgebra.Hom

variable {R : Type u} [CommRing R]
variable {A : CochainDGAlgebra.{u, v} R} {B : CochainDGAlgebra.{u, w} R}

/-- Restriction of scalars preserves quasi-isomorphisms and therefore descends through the
canonical Verdier localizations of differential graded modules. -/
theorem restriction_inverts (f : Hom A B) :
    (DifferentialGradedModule.quasiIso.{u, x} B).IsInvertedBy
      (f.restrictDgFunctor.mapK ⋙ DifferentialGradedModule.Derived.Q A) := sorry

namespace Derived

/-- Canonical derived restriction of scalars along `f`. -/
@[stacks 0BYX "canonical derived restriction of scalars"]
noncomputable def restriction (f : Hom A B) :
    CategoryTheory.Functor
      (DifferentialGradedModule.Derived.Category.{u, x} B)
      (DifferentialGradedModule.Derived.Category.{u, x} A) :=
  Localization.lift
    (f.restrictDgFunctor.mapK ⋙ DifferentialGradedModule.Derived.Q A)
    (restriction_inverts f) (DifferentialGradedModule.Derived.Q B)

/-- Canonical derived restriction factors ordinary restriction through the localization
functors. -/
@[stacks 0BYZ "canonical factorization of derived restriction of scalars"]
noncomputable def restrictionFac (f : Hom A B) :
    DifferentialGradedModule.Derived.Q B ⋙ restriction f ≅
      f.restrictDgFunctor.mapK ⋙ DifferentialGradedModule.Derived.Q A :=
  Localization.fac
    (f.restrictDgFunctor.mapK ⋙ DifferentialGradedModule.Derived.Q A)
    (restriction_inverts f) (DifferentialGradedModule.Derived.Q B)

/-- Derived restriction is the canonical localization lift of ordinary restriction of
scalars. -/
@[stacks 0BYZ "lifting property of derived restriction of scalars"]
noncomputable instance restrictionLifting (f : Hom A B) :
    Localization.Lifting
      (DifferentialGradedModule.Derived.Q B)
      (DifferentialGradedModule.quasiIso B)
      (f.restrictDgFunctor.mapK ⋙ DifferentialGradedModule.Derived.Q A)
      (restriction f) :=
  ⟨restrictionFac f⟩

/-- Derived restriction of scalars is additive. -/
@[stacks 0BYX "additivity of derived restriction of scalars"]
noncomputable instance restrictionAdditive (f : Hom A B) :
    (restriction f).Additive := sorry

/-- Derived restriction of scalars is `R`-linear. -/
@[stacks 0BYX "linearity of derived restriction of scalars"]
noncomputable instance restrictionLinear (f : Hom A B) :
    Functor.Linear R (restriction f) := sorry

end Derived

variable (f : Hom A B)

#synth (Derived.restriction f).Additive
#synth Functor.Linear R (Derived.restriction f)

end CochainDGAlgebra.Hom
