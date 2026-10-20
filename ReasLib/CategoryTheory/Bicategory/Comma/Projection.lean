module

public import ReasLib.CategoryTheory.Bicategory.Comma.Projection.Endpoint
public import ReasLib.CategoryTheory.Bicategory.Comma.Projection.Comparison
public import ReasLib.CategoryTheory.Bicategory.Comma.Projection.Lift

/-!
# Projections and lifts of colax comma bicategories

Compatibility aggregate for the colax comma projection hierarchy.

- `Comma.Projection.Endpoint` owns the left and right endpoint pseudofunctors;
- `Comma.Projection.Comparison` owns their universal oplax comparison;
- `Comma.Projection.Lift` owns factorization of an oplax square through the
  colax comma bicategory.

Existing users may continue to import this module. New developments can import
the smallest leaf that provides the required construction.
-/
