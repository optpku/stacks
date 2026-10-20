module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.CategoryTheory.ObjectProperty.ClosedUnderIsomorphisms
public import ReasLib.Algebra.Homology.CochainComplex.FiniteProjective
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat
import Mathlib.Tactic.CrossRefAttribute

/-!
# Perfect complexes

@stack 0657

This file owns bounded finite-projective and perfect predicates for module cochain complexes and
their derived categories.
-/

@[expose] public section

noncomputable section

open CategoryTheory

universe u

variable {R : Type u} [Ring R]

namespace DerivedCategory

/-- An object of `D(R)` is perfect if it is isomorphic in the derived category to a bounded
cochain complex of finite projective `R`-modules. -/
@[stacks 0657 "(1), perfect derived object"]
def IsPerfect (K : DerivedCategory (ModuleCat R)) : Prop :=
  ∃ (L : CochainComplex (ModuleCat R) ℤ) (_ : K ≅ DerivedCategory.Q.obj L),
    CochainComplex.IsBoundedFiniteProjective L

/-- Perfectness of derived objects is invariant under isomorphism. -/
@[stacks 0657 "perfect derived objects are closed under isomorphisms"]
instance isPerfect_isClosedUnderIsomorphisms :
    ObjectProperty.IsClosedUnderIsomorphisms
      (IsPerfect : ObjectProperty (DerivedCategory (ModuleCat R))) := sorry

end DerivedCategory

namespace ModuleCat

/-- An `R`-module is perfect if its degree-zero complex is a perfect object of `D(R)`. -/
@[stacks 0657 "(2), perfect module"]
abbrev IsPerfect (M : ModuleCat R) : Prop :=
  DerivedCategory.IsPerfect ((DerivedCategory.singleFunctor (ModuleCat R) (0 : ℤ)).obj M)

end ModuleCat
