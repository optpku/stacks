/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DifferentialGradedModule.Derived
public import Mathlib.Tactic.CrossRefAttribute

/-!
# The canonical functor from differential graded modules to the derived category

This leaf owns the composite of passage to homotopy classes with Verdier localization.  Keeping
this functor independent of limits lets constructions such as delta functors depend only on the
derived-category foundation they actually use.
-/

@[expose] public section

noncomputable section

universe u v w

open CategoryTheory DifferentialGradedCategory

namespace DifferentialGradedModule.Derived

variable {R : Type u} [CommRing R]
variable {A : CochainDGAlgebra.{u, w} R}

/-- The canonical functor from differential graded modules to their derived category. -/
@[stacks 09KX "canonical functor from DG modules to the derived category"]
def fromModules (A : CochainDGAlgebra.{u, w} R) :
    DifferentialGradedModule.{u, v} A ⥤ Category.{u, v} A :=
  toK A ⋙ Q A

/-- The canonical functor from differential graded modules to their derived category is
additive. -/
@[stacks 09KX "additivity of the canonical functor to the derived category"]
instance fromModulesAdditive (A : CochainDGAlgebra.{u, w} R) :
    (fromModules.{u, v} A).Additive := sorry

/-- The canonical functor from differential graded modules to their derived category is
`R`-linear. -/
@[stacks 09KX "linearity of the canonical functor to the derived category"]
noncomputable instance fromModulesLinear (A : CochainDGAlgebra.{u, w} R) :
    Functor.Linear R (fromModules.{u, v} A) := sorry

/-- The image of a differential graded module is represented by the same module after
localization. -/
@[stacks 09RA "strict-module derived-image object computation", simp]
theorem fromModules_obj (A : CochainDGAlgebra.{u, w} R)
    (M : DifferentialGradedModule.{u, v} A) :
    (fromModules A).obj M =
      (Q A).obj (⟨M⟩ : K R (DifferentialGradedModule.{u, v} A)) := sorry

/-- The module-to-derived functor maps a morphism through its represented homotopy class. -/
@[stacks 09RA "strict-module derived-image morphism computation", simp]
theorem fromModules_map (A : CochainDGAlgebra.{u, w} R)
    {M N : DifferentialGradedModule.{u, v} A} (f : M ⟶ N) :
    (fromModules A).map f = (Q A).map ((toK A).map f) := sorry

/-- Derived homology of a strict DG-module agrees with its ordinary DG-module homology.  This
objectwise comparison is the canonical bridge used by representation-facing window and
countability APIs. -/
@[stacks 09RA "strict-module comparison for derived homology"]
noncomputable def homologyIso (A : CochainDGAlgebra.{u, w} R)
    (M : DifferentialGradedModule.{u, v} A) (n : ℤ) :
    (homologyFunctor A n).obj ((fromModules A).obj M) ≅ M.homology n :=
  (homologyFunctorFactors A n).app ((toK A).obj M) ≪≫
    Homotopy.homologyIso A M n

/-- The homotopy-to-derived localization is essentially surjective. -/
@[stacks 09KX "essential surjectivity of homotopy-to-derived localization"]
instance qEssSurj (A : CochainDGAlgebra.{u, w} R) : (Q.{u, v} A).EssSurj := sorry

#synth (fromModules.{u, v} A).Additive
#synth Functor.Linear R (fromModules.{u, v} A)

end DifferentialGradedModule.Derived
