module

public import Mathlib.CategoryTheory.Sites.Limits

/-!
# Colimits of Type-valued sheaves

Mathlib's generic `Sheaf` colimit instance already derives all colimits of
`Type`-valued sheaves from the coefficient category.  This compatibility
import deliberately adds no project instance: downstream code should use the
canonical Mathlib instance and avoid typeclass overlap.
-/
