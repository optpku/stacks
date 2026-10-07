module

public import ReasLib.CategoryTheory.Fibered.Groupoids.TwoYoneda.Presheaf
public import ReasLib.CategoryTheory.Fibered.Groupoids.TwoYoneda.SplitModel
public import ReasLib.CategoryTheory.Fibered.Groupoids.TwoYoneda.Comparison

/-!
# Two-dimensional Yoneda strictification

Compatibility aggregate for the Cat-valued two-Yoneda presheaf, its canonical split
co-Grothendieck model, evaluation at the identity, and its equivalence properties. The comparison
API is split between `Comparison.Construction` and `Comparison.Equivalence`; new direct users
should import the narrow leaf that owns the required layer.
-/
