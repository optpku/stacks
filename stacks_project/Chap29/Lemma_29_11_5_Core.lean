module

public import ReasLib.AlgebraicGeometry.Scheme.QuasiCoherentAlgebra.Basic

/-!
# Lemma 29.11.5 core compatibility entry point

The reusable category of quasi-coherent algebra sheaves is owned by
`ReasLib.AlgebraicGeometry.Scheme.QuasiCoherentAlgebra.Basic`.
-/

/- Lemma 29.11.5: quasi-coherent `𝒪_S`-algebras and their forgetful functor. -/
#check @AlgebraicGeometry.Scheme.schemeCommRingSheaf
#check @AlgebraicGeometry.Scheme.qcAlgebraUnderProperty
#check @AlgebraicGeometry.Scheme.QcAlgebraUnder
#check @AlgebraicGeometry.Scheme.QcAlgebraUnder.forget
#check @AlgebraicGeometry.Scheme.QcAlgebraUnder.isQuasicoherent_restrictedUnit
