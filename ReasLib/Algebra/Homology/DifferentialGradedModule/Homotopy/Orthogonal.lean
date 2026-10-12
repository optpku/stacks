/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.ObjectProperty.Orthogonal
public import ReasLib.Algebra.Homology.DifferentialGradedModule.Derived

/-!
# K-projective and K-injective differential graded modules

The canonical definitions are the left and right orthogonals of acyclic objects in the intrinsic
DG homotopy category.
-/

@[expose] public section

universe u v

open CategoryTheory DifferentialGradedCategory
open scoped DifferentialGradedCategory

namespace DifferentialGradedModule.Homotopy

variable {R : Type u} [CommRing R]
variable (A : CochainDGAlgebra.{u, v} R)

/-- K-projective objects in the intrinsic homotopy category are left orthogonal to all acyclic
objects. -/
@[stacks 09KM "K-projective differential graded modules"]
def kProjective : ObjectProperty (K R (DifferentialGradedModule.{u, v} A)) :=
  (acyclic A).leftOrthogonal

/-- K-injective objects in the intrinsic homotopy category are right orthogonal to all acyclic
objects. -/
@[stacks 09KS "K-injective differential graded modules"]
def kInjective : ObjectProperty (K R (DifferentialGradedModule.{u, v} A)) :=
  (acyclic A).rightOrthogonal

/-- An object is K-projective exactly when every map from it to an acyclic object is zero. -/
theorem kProjective_iff (P : K R (DifferentialGradedModule.{u, v} A)) :
    kProjective A P ↔
      ∀ ⦃N : K R (DifferentialGradedModule.{u, v} A)⦄ (f : P ⟶ N),
        acyclic A N → f = 0 := sorry

/-- An object is K-injective exactly when every map to it from an acyclic object is zero. -/
theorem kInjective_iff (I : K R (DifferentialGradedModule.{u, v} A)) :
    kInjective A I ↔
      ∀ ⦃N : K R (DifferentialGradedModule.{u, v} A)⦄ (f : N ⟶ I),
        acyclic A N → f = 0 := sorry

end DifferentialGradedModule.Homotopy
