/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.CochainDGAlgebra.Bounded
public import ReasLib.Algebra.Homology.DifferentialGradedModule.Derived.Limits
public import ReasLib.Algebra.Homology.DifferentialGradedModule.Graded.FiniteProjective
public import ReasLib.Algebra.Homology.DifferentialGradedModule.Homotopy.KProjective
public import ReasLib.CategoryTheory.Preadditive.CompactObject

/-!
# Finite K-Projective Models of Compact Derived Objects

This leaf owns the finite K-projective object property and its compactness comparison.  Over a
bounded cochain DGA, compact derived objects form precisely the essential image of this property.
-/

@[expose] public section

noncomputable section

universe u v

open CategoryTheory DifferentialGradedCategory
open scoped DifferentialGradedCategory

namespace DifferentialGradedModule

variable {R : Type u} [CommRing R]
variable (A : CochainDGAlgebra.{u, v} R)

/-- Finite K-projective DG-modules are finite projective after forgetting the differential and
K-projective in the intrinsic DG homotopy category. -/
@[stacks 09RB "finite graded K-projective differential graded modules"]
def finiteKProjective : ObjectProperty (DifferentialGradedModule.{u, v} A) :=
  fun P ↦ IsFiniteGradedProjective A P ∧ IsKProjective A P

/-- The two defining properties of a finite K-projective DG-module. -/
@[stacks 09RB "finite K-projective defining-property criterion"]
theorem finiteKProjective_iff (P : DifferentialGradedModule.{u, v} A) :
    finiteKProjective A P ↔ IsFiniteGradedProjective A P ∧ IsKProjective A P := sorry

/-- Finite K-projectivity is finite graded projectivity together with bijectivity of localization
on every outgoing Hom set.  This is the representation-facing criterion used to construct and
recognize compact derived objects. -/
@[stacks 09RB]
theorem finiteKProjective_iff_q_map_bijective
    (P : DifferentialGradedModule.{u, v} A) :
    finiteKProjective A P ↔
      IsFiniteGradedProjective A P ∧
        ∀ M : DifferentialGradedModule.{u, v} A,
          Function.Bijective
            ((Derived.Q A).map :
              ((toK A).obj P ⟶ (toK A).obj M) →
                ((Derived.fromModules A).obj P ⟶ (Derived.fromModules A).obj M)) := sorry

namespace FiniteKProjective

/-- Finite K-projective DG-modules are stable under retracts. -/
@[stacks 09RB "retract stability of finite K-projective modules"]
instance isStableUnderRetracts :
    (finiteKProjective A).IsStableUnderRetracts := sorry

end FiniteKProjective

namespace Derived.FiniteKProjective

/-- Remark 22.36.2 (09R1): a finite graded K-projective DG-module has compact image in the
derived category. -/
@[stacks 09R1]
theorem isCompactObject {P : DifferentialGradedModule.{u, v} A}
    (hP : finiteKProjective A P) : IsCompactObject ((Derived.fromModules A).obj P) := sorry

/-- Lemma 22.36.6 (09RB): over a bounded DGA, compact derived objects are precisely the essential
image of finite graded K-projective DG-modules. -/
@[stacks 09RB]
theorem isCompactObject_iff (hA : A.IsBounded) (E : Derived.Category.{u, v} A) :
    IsCompactObject E ↔ (finiteKProjective A).map (Derived.fromModules A) E := sorry

/-- The representative formulation of compactness by finite graded K-projective DG-modules over
a bounded DGA. -/
@[stacks 09RB "compactness represented by a finite K-projective module"]
theorem isCompactObject_iff_exists (hA : A.IsBounded) (E : Derived.Category.{u, v} A) :
    IsCompactObject E ↔
      ∃ (P : DifferentialGradedModule.{u, v} A),
        IsFiniteGradedProjective A P ∧ IsKProjective A P ∧
          Nonempty ((Derived.fromModules A).obj P ≅ E) := sorry

end Derived.FiniteKProjective

#synth (finiteKProjective A).IsStableUnderRetracts
#synth (finiteKProjective A).IsClosedUnderIsomorphisms

end DifferentialGradedModule
