module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Complex.Flat
public import ReasLib.Algebra.Homology.CochainComplex.KFlat

/-!
# Termwise flatness and K-flatness

Termwise flatness and K-flatness are independent canonical predicates.  In particular, their
conjunction has no additional mathematical structure and should be written directly rather than
hidden behind a ringed-site-specific wrapper.
-/

@[expose] public section

open CategoryTheory

noncomputable section
