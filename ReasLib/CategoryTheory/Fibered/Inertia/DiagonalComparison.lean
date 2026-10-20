module

public import ReasLib.CategoryTheory.Fibered.Inertia.DiagonalComparison.RelativeDiagonal
public import ReasLib.CategoryTheory.Fibered.Inertia.DiagonalComparison.Comparison
public import ReasLib.CategoryTheory.Fibered.Inertia.DiagonalComparison.Inverse
public import ReasLib.CategoryTheory.Fibered.Inertia.DiagonalComparison.Unit
public import ReasLib.CategoryTheory.Fibered.Inertia.DiagonalComparison.Counit
public import ReasLib.CategoryTheory.Fibered.Inertia.DiagonalComparison.Equivalence

/-!
# Relative inertia and the relative diagonal

Compatibility aggregate for the relative diagonal, its canonical comparison with relative
inertia, an explicit inverse, and the unit/counit equivalence data. New users can import the
smallest corresponding leaf module directly. The preferred readout is grouped under
`BasedFunctor.RelativeInertia.diagonalComparison` together with its
`{inverse,unitIso,counitIso,quasiInverse}` API and
`BasedFunctor.relativeDiagonal`.
-/
