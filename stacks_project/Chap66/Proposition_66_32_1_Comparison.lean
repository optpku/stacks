module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.SchemeComparison

/-! Compatibility facade for the canonical scheme/quasi-coherent module comparison. -/

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

#check (AlgebraicGeometry.AlgebraicSpace.QCoh.restrictToScheme :
  ∀ {S : Scheme.{u}} (U : Over S), QCoh (ofOver U) ⥤ Scheme.QCoh U.left)
