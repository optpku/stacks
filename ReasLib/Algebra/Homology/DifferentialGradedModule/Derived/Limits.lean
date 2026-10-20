/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DifferentialGradedModule.Derived.FromModules
public import ReasLib.Algebra.Homology.DifferentialGradedModule.Homotopy.Limits
public import ReasLib.CategoryTheory.Limits.EssentiallySurjective
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Products and coproducts of differential graded modules after localization

Products and coproducts of differential graded modules descend from the single homotopy-limit
owner and then through Verdier localization.  The existence instances below are constructed
through the generic essentially-surjective-functor API; only preservation and acyclicity
statements carry proof debt.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits DifferentialGradedCategory

noncomputable section

universe u v w x

namespace DifferentialGradedModule

variable {R : Type u} [CommRing R]
variable {A : CochainDGAlgebra.{u, x} R}

namespace Homotopy

namespace Acyclic

/-- A coproduct of acyclic differential graded modules in the homotopy category is acyclic. -/
theorem coproduct (A : CochainDGAlgebra.{u, x} R) {J : Type v}
    (X : J → K R (DifferentialGradedModule.{u, max v w} A)) [HasCoproduct X]
    (hX : ∀ j, acyclic A (X j)) :
    acyclic A (∐ X) := sorry

/-- A product of acyclic differential graded modules in the homotopy category is acyclic. -/
theorem product (A : CochainDGAlgebra.{u, x} R) {J : Type v}
    (X : J → K R (DifferentialGradedModule.{u, max v w} A)) [HasProduct X]
    (hX : ∀ j, acyclic A (X j)) :
    acyclic A (∏ᶜ X) := sorry

end Acyclic

end Homotopy

namespace Derived

namespace Coproduct

/-- Localization from the homotopy category preserves coproducts. -/
instance qPreserves (A : CochainDGAlgebra.{u, x} R) (J : Type v) :
    PreservesColimitsOfShape (Discrete J) (Q.{u, max v w} A) := sorry

/-- Lemma 22.22.4 (1), coproduct part (09QI): the derived category of a differential graded
algebra has coproducts of every shape available for differential graded modules. -/
@[stacks 09QI "coproducts in the DG-module derived category"]
noncomputable instance hasCoproductsOfShape
    (A : CochainDGAlgebra.{u, x} R) (J : Type v) :
    HasCoproductsOfShape J (Category.{u, max v w} A) :=
  Functor.EssSurj.hasCoproductsOfShape (Q.{u, max v w} A)

/-- Lemma 22.22.4 (2) (09QI): the canonical functor from differential graded modules to the
derived category preserves coproducts. -/
@[stacks 09QI "DG-module coproduct model"]
instance fromModulesPreserves (A : CochainDGAlgebra.{u, x} R) (J : Type v) :
    PreservesColimitsOfShape (Discrete J) (fromModules.{u, max v w} A) := sorry

end Coproduct

namespace Product

/-- Localization from the homotopy category preserves products. -/
instance qPreserves (A : CochainDGAlgebra.{u, x} R) (J : Type v) :
    PreservesLimitsOfShape (Discrete J) (Q.{u, max v w} A) := sorry

/-- Lemma 22.22.4 (1), product part (09QI): the derived category of a differential graded algebra
has products of every shape available for differential graded modules. -/
@[stacks 09QI "products in the DG-module derived category"]
noncomputable instance hasProductsOfShape
    (A : CochainDGAlgebra.{u, x} R) (J : Type v) :
    HasProductsOfShape J (Category.{u, max v w} A) :=
  Functor.EssSurj.hasProductsOfShape (Q.{u, max v w} A)

/-- Lemma 22.22.4 (3) (09QI): the canonical functor from differential graded modules to the
derived category preserves products. -/
@[stacks 09QI "DG-module product model"]
instance fromModulesPreserves (A : CochainDGAlgebra.{u, x} R) (J : Type v) :
    PreservesLimitsOfShape (Discrete J) (fromModules.{u, max v w} A) := sorry

end Product

#synth (fromModules.{u, max v w} A).Additive

end Derived

end DifferentialGradedModule
