module

public import ReasLib.AlgebraicGeometry.Scheme.Normalization.FiniteComponents
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Birational.Integral

/-!
# Normal schemes and normalization

This file relates normality of schemes to the canonical normalization morphism.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme

/-- For a scheme with finitely many irreducible components on quasi-compact opens, the canonical
normalization morphism is an isomorphism if and only if the scheme is normal. -/
theorem isIso_normalizationTo_iff_isNormal
    (X : Scheme.{u}) [HasFiniteIrreducibleComponentsOnCompactOpens X] :
    IsIso X.normalizationTo ↔ X.isNormal := sorry

end AlgebraicGeometry.Scheme
