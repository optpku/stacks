module

public import ReasLib.AlgebraicGeometry.Scheme.DeRham.Gysin.Cohomology.Differential

@[expose] public section

open AlgebraicGeometry CategoryTheory

/- Compatibility bridge for the Hodge cohomology differential used by later Chapter 50 items. -/
#check (AlgebraicGeometry.Scheme.DeRham.hodgeDifferential :
    ∀ {X S : Scheme} (f : X ⟶ S) (p q : ℕ),
      AlgebraicGeometry.Scheme.DeRham.hodgeCohomologyObject f p (q : ℤ) ⟶
        AlgebraicGeometry.Scheme.DeRham.hodgeCohomologyObject f (p + 1) (q : ℤ))
