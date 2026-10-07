module

public import ReasLib.CategoryTheory.Fibered.CategoryHomology
public import ReasLib.CategoryTheory.Fibered.CategoryHomology.Bar.Complex
public import ReasLib.CategoryTheory.Fibered.CategoryHomology.Bar.DeltaFunctor
public import ReasLib.CategoryTheory.Fibered.CategoryHomology.Bar.LeftDerived

/-!
# Fiber Bar homology facade

This facade exports the object-level fiber Bar API together with its chain-level, delta-functor,
and projective computation leaves.  The object-level owner remains in
`Fibered.CategoryHomology`; the dependent leaves intentionally do not import this facade.
-/

@[expose] public section
