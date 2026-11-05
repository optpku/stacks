module

public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.CategoryTheory.ObjectProperty.ClosedUnderIsomorphisms
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Cochain Complexes with a Fixed Strict Bound

This file packages strict upper and lower bounds at a specified degree as
object properties and full subcategories of cochain complexes.  Unlike
`CochainComplex.Minus` and `CochainComplex.Plus`, these categories retain the
cutoff as part of their type, so downstream constructions can recover the
corresponding `IsStrictlyLE` or `IsStrictlyGE` instance canonically.
-/

@[expose] public section

open CategoryTheory Limits

universe v u

namespace CochainComplex

variable (C : Type u) [Category.{v} C] [HasZeroMorphisms C]

/-- The object property of cochain complexes strictly supported in degrees at
most the fixed cutoff `n`. -/
@[stacks 0159 "strict upper bound at a fixed degree"]
def strictlyLE (n : ℤ) : ObjectProperty (CochainComplex C ℤ) :=
  fun K => K.IsStrictlyLE n

/-- Membership in `strictlyLE C n` is the canonical strict upper-bound
condition at `n`. -/
@[stacks 0159 "membership in a fixed strict upper bound"]
theorem strictlyLE_iff (n : ℤ) (K : CochainComplex C ℤ) :
    strictlyLE C n K ↔ K.IsStrictlyLE n := sorry

/-- The full subcategory of cochain complexes strictly supported in degrees
at most the fixed cutoff `n`. -/
@[stacks 0159 "cochain complexes with a fixed strict upper bound"]
abbrev StrictlyLE (n : ℤ) :=
  (strictlyLE C n).FullSubcategory

namespace StrictlyLE

variable {C}

/-- The fixed strict upper-bound property is invariant under isomorphisms of
cochain complexes. -/
@[stacks 0159 "fixed strict upper bounds are invariant under isomorphism"]
instance isClosedUnderIsomorphisms (n : ℤ) :
    (strictlyLE C n).IsClosedUnderIsomorphisms := sorry

variable (C) in
/-- The inclusion of cochain complexes with fixed strict upper bound `n` into
all cochain complexes. -/
@[stacks 0159 "inclusion of complexes with a fixed strict upper bound"]
def inclusion (n : ℤ) : StrictlyLE C n ⥤ CochainComplex C ℤ :=
  (strictlyLE C n).ι

/-- The underlying complex of a bundled fixed-upper-bound object carries its
canonical strict upper-bound instance. -/
@[stacks 0159 "canonical fixed strict upper-bound instance"]
instance isStrictlyLE (n : ℤ) (K : StrictlyLE C n) :
    K.obj.IsStrictlyLE n := sorry

/-- Bundle a cochain complex equipped with a strict upper bound at the fixed
cutoff `n`. -/
@[stacks 0159 "bundle a complex with a fixed strict upper bound"]
def ofBounds (K : CochainComplex C ℤ) (n : ℤ) [bound : K.IsStrictlyLE n] :
    StrictlyLE C n :=
  ⟨K, bound⟩

/-- The fixed-upper-bound inclusion retains the underlying cochain complex. -/
@[simp, stacks 0159 "object computation for fixed strict upper bounds"]
theorem inclusion_obj (n : ℤ) (K : StrictlyLE C n) :
    (inclusion C n).obj K = K.obj := sorry

/-- The fixed-upper-bound inclusion retains the underlying morphism. -/
@[simp, stacks 0159 "morphism computation for fixed strict upper bounds"]
theorem inclusion_map (n : ℤ) {K L : StrictlyLE C n} (f : K ⟶ L) :
    (inclusion C n).map f = f.hom := sorry

/-- Bundling a complex with its fixed strict upper bound retains that complex
as the underlying object. -/
@[simp, stacks 0159 "object computation for fixed strict upper-bound bundling"]
theorem ofBounds_obj (K : CochainComplex C ℤ) (n : ℤ) [K.IsStrictlyLE n] :
    (ofBounds K n).obj = K := sorry

end StrictlyLE

/-- The object property of cochain complexes strictly supported in degrees at
least the fixed cutoff `n`. -/
@[stacks 0159 "strict lower bound at a fixed degree"]
def strictlyGE (n : ℤ) : ObjectProperty (CochainComplex C ℤ) :=
  fun K => K.IsStrictlyGE n

/-- Membership in `strictlyGE C n` is the canonical strict lower-bound
condition at `n`. -/
@[stacks 0159 "membership in a fixed strict lower bound"]
theorem strictlyGE_iff (n : ℤ) (K : CochainComplex C ℤ) :
    strictlyGE C n K ↔ K.IsStrictlyGE n := sorry

/-- The full subcategory of cochain complexes strictly supported in degrees
at least the fixed cutoff `n`. -/
@[stacks 0159 "cochain complexes with a fixed strict lower bound"]
abbrev StrictlyGE (n : ℤ) :=
  (strictlyGE C n).FullSubcategory

namespace StrictlyGE

variable {C}

/-- The fixed strict lower-bound property is invariant under isomorphisms of
cochain complexes. -/
@[stacks 0159 "fixed strict lower bounds are invariant under isomorphism"]
instance isClosedUnderIsomorphisms (n : ℤ) :
    (strictlyGE C n).IsClosedUnderIsomorphisms := sorry

variable (C) in
/-- The inclusion of cochain complexes with fixed strict lower bound `n` into
all cochain complexes. -/
@[stacks 0159 "inclusion of complexes with a fixed strict lower bound"]
def inclusion (n : ℤ) : StrictlyGE C n ⥤ CochainComplex C ℤ :=
  (strictlyGE C n).ι

/-- The underlying complex of a bundled fixed-lower-bound object carries its
canonical strict lower-bound instance. -/
@[stacks 0159 "canonical fixed strict lower-bound instance"]
instance isStrictlyGE (n : ℤ) (K : StrictlyGE C n) :
    K.obj.IsStrictlyGE n := sorry

/-- Bundle a cochain complex equipped with a strict lower bound at the fixed
cutoff `n`. -/
@[stacks 0159 "bundle a complex with a fixed strict lower bound"]
def ofBounds (K : CochainComplex C ℤ) (n : ℤ) [bound : K.IsStrictlyGE n] :
    StrictlyGE C n :=
  ⟨K, bound⟩

/-- The fixed-lower-bound inclusion retains the underlying cochain complex. -/
@[simp, stacks 0159 "object computation for fixed strict lower bounds"]
theorem inclusion_obj (n : ℤ) (K : StrictlyGE C n) :
    (inclusion C n).obj K = K.obj := sorry

/-- The fixed-lower-bound inclusion retains the underlying morphism. -/
@[simp, stacks 0159 "morphism computation for fixed strict lower bounds"]
theorem inclusion_map (n : ℤ) {K L : StrictlyGE C n} (f : K ⟶ L) :
    (inclusion C n).map f = f.hom := sorry

/-- Bundling a complex with its fixed strict lower bound retains that complex
as the underlying object. -/
@[simp, stacks 0159 "object computation for fixed strict lower-bound bundling"]
theorem ofBounds_obj (K : CochainComplex C ℤ) (n : ℤ) [K.IsStrictlyGE n] :
    (ofBounds K n).obj = K := sorry

end StrictlyGE




end CochainComplex
