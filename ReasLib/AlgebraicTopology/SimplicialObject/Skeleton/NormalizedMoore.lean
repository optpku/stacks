module

public import ReasLib.AlgebraicTopology.SimplexCategory.Truncated.KanExtension.FiniteConnected
public import ReasLib.AlgebraicTopology.SimplicialObject.DoldKan.LowerFace
public import ReasLib.AlgebraicTopology.SimplicialObject.Skeleton.Generated
public import Mathlib.Tactic.CrossRefAttribute

/-!
@stack 017Y

# Normalized Moore complexes of simplicial skeleta

The bounded-degree generated object and the left Kan extension of an `m`-truncated simplicial
object have no normalized Moore part above degree `m`. The source-facing theorems use the
lower-face convention; symmetric upper-face companions remain available for Mathlib consumers.
-/

@[expose] public section

open CategoryTheory Opposite AlgebraicTopology
open scoped Simplicial

universe u v

namespace CategoryTheory.SimplicialObject

namespace generated

variable {A : Type u} [Category.{v} A] [Abelian A]

/-- The upper-face normalized Moore subobject of the bounded-degree generated simplicial object
vanishes above the generating bound. -/
@[stacks 017Y "upper-face normalized Moore vanishing companion"]
theorem normalizedMoore.eq_bot_of_lt (U : SimplicialObject A) {n m : ℕ} (h : n < m) :
    NormalizedMooreComplex.objX (U.generated n : SimplicialObject A) m = ⊥ := sorry

/-- The upper-face normalized Moore object of a bounded-degree generated simplicial object is
zero above the generating bound. -/
@[stacks 017Y "upper-face normalized Moore zero object above the generating degree"]
theorem normalizedMoore.isZero_of_lt (U : SimplicialObject A) {n m : ℕ} (h : n < m) :
    CategoryTheory.Limits.IsZero
      (NormalizedMooreComplex.objX (U.generated n : SimplicialObject A) m : A) := sorry

namespace normalizedMoore.lowerFace

/-- The lower-face normalized Moore subobject of the bounded-degree generated simplicial object
vanishes above the generating bound. -/
@[stacks 017Y "lower-face normalized Moore vanishing above the generating degree"]
theorem eq_bot_of_lt (U : SimplicialObject A) {n m : ℕ} (h : n < m) :
    SimplicialObject.normalizedMoore.lowerFace.subobject
      (U.generated n : SimplicialObject A) m = ⊥ := sorry

/-- The lower-face normalized Moore object of a bounded-degree generated simplicial object is
zero above the generating bound. -/
@[stacks 017Y "lower-face normalized Moore zero object above the generating degree"]
theorem isZero_of_lt (U : SimplicialObject A) {n m : ℕ} (h : n < m) :
    CategoryTheory.Limits.IsZero
      (SimplicialObject.normalizedMoore.lowerFace.subobject
        (U.generated n : SimplicialObject A) m : A) := sorry

end normalizedMoore.lowerFace

end generated

namespace Truncated

variable {A : Type u} [Category.{v} A] [Abelian A]

/-- The upper-face normalized Moore subobject of the simplicial skeleton of an `m`-truncated
object vanishes in every degree strictly greater than `m`. -/
@[stacks 018T "upper-face normalized Moore vanishing companion"]
theorem sk.normalizedMoore.eq_bot_of_lt {m : ℕ} (U : SimplicialObject.Truncated A m)
    {n : ℕ} (h : m < n) :
    NormalizedMooreComplex.objX ((Truncated.sk m).obj U) n = ⊥ := sorry

/-- The upper-face normalized Moore object of a simplicial skeleton is zero above its truncation
degree. -/
@[stacks 018T "upper-face normalized Moore zero object above a simplicial skeleton"]
theorem sk.normalizedMoore.isZero_of_lt {m : ℕ} (U : SimplicialObject.Truncated A m)
    {n : ℕ} (h : m < n) :
    CategoryTheory.Limits.IsZero
      (NormalizedMooreComplex.objX ((Truncated.sk m).obj U) n : A) := sorry

namespace sk.normalizedMoore.lowerFace

/-- The lower-face normalized Moore subobject of the simplicial skeleton of an `m`-truncated object
vanishes in every degree strictly greater than `m`. -/
@[stacks 018T "lower-face normalized Moore vanishing above a simplicial skeleton"]
theorem eq_bot_of_lt {m : ℕ} (U : SimplicialObject.Truncated A m)
    {n : ℕ} (h : m < n) :
    SimplicialObject.normalizedMoore.lowerFace.subobject ((Truncated.sk m).obj U) n = ⊥ := sorry

/-- The lower-face normalized Moore object of a simplicial skeleton is zero above its truncation
degree. -/
@[stacks 018T "lower-face normalized Moore zero object above a simplicial skeleton"]
theorem isZero_of_lt {m : ℕ} (U : SimplicialObject.Truncated A m)
    {n : ℕ} (h : m < n) :
    CategoryTheory.Limits.IsZero
      (SimplicialObject.normalizedMoore.lowerFace.subobject
        ((Truncated.sk m).obj U) n : A) := sorry

end sk.normalizedMoore.lowerFace

end Truncated

end CategoryTheory.SimplicialObject
