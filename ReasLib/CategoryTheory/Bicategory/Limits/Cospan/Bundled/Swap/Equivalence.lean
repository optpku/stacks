module

public import ReasLib.CategoryTheory.Bicategory.Limits.Cospan.Bundled.Swap.Computations
public import ReasLib.CategoryTheory.Bicategory.StrictPseudofunctor.Inverse

/-!
# Biequivalence of bundled cospan swap

The strict endpoint swap is its own equality-level inverse. This file exposes that fact through
the generic strict-inverse certificate and registers the resulting biequivalence for typeclass
search.
-/

@[expose] public section

open scoped CategoryTheory.Bicategory

universe w v u

namespace CategoryTheory.Bicategory.Cospan

/-- Bundled cospan swap is its own strict inverse on objects, `1`-morphisms, and
`2`-morphisms. -/
@[stacks 0040 "strict involutivity of bundled bicategorical cospan swap"]
theorem swap.isStrictInverse (B : Type u) [Bicategory.{w, v} B] :
    StrictPseudofunctor.IsStrictInverse (Cospan.swap B) (Cospan.swap B) := sorry

/-- Forgetting the strict structure, bundled cospan swap is a biequivalence. -/
instance swap.isBiequivalence (B : Type u) [Bicategory.{w, v} B] :
    Pseudofunctor.IsBiequivalence (Cospan.swap B).toPseudofunctor := sorry

end CategoryTheory.Bicategory.Cospan
