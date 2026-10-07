module

public import ReasLib.CategoryTheory.Bicategory.FullSubbicategory.Lift.Construction
public import ReasLib.CategoryTheory.Bicategory.FullSubbicategory.Lift.Computations
public import ReasLib.CategoryTheory.Bicategory.FullSubbicategory.Lift.Comparisons
public import ReasLib.CategoryTheory.Bicategory.FullSubbicategory.Lift.Inverse
public import ReasLib.CategoryTheory.Bicategory.FullSubbicategory.Lift.LocalProperties

/-!
# Lifts to full subbicategories

Compatibility aggregate for strict pseudofunctor lifts and the local-equivalence
facts of property-implication inclusions.  New developments can import
`FullSubbicategory.Lift.Construction` when only the construction is needed, or
`FullSubbicategory.Lift.Computations` when only the readout and factorization
API is needed. Comparison-cell readouts live in
`FullSubbicategory.Lift.Comparisons`. Strict inverse certificates restricted
to stable object properties are provided by `FullSubbicategory.Lift.Inverse`.
-/
