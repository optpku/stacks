module

public import ReasLib.AlgebraicGeometry.Scheme.GenericPoints.FiniteComponents
public import ReasLib.AlgebraicGeometry.Scheme.ObjectProperty.AffineDescent
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Fppf.Comparison

@[expose] public section

universe u

namespace AlgebraicGeometry.Scheme.HasFiniteIrreducibleComponentsOnCompactOpens

/-- The property that every quasi-compact open subscheme has finitely many irreducible
components is local for the fppf precoverage. -/
instance isLocalFppf :
    CategoryTheory.ObjectProperty.IsLocal
      (fun X : Scheme.{u} ↦ HasFiniteIrreducibleComponentsOnCompactOpens X)
      Scheme.fppfPrecoverage := sorry

/-- The scheme-level property that every quasi-compact open has finitely many irreducible
components is local for the étale precoverage. -/
instance isLocalEtale :
    CategoryTheory.ObjectProperty.IsLocal
      (fun U : Scheme.{u} ↦ Scheme.HasFiniteIrreducibleComponentsOnCompactOpens U)
      Scheme.etalePrecoverage :=
  CategoryTheory.ObjectProperty.IsLocal.of_le Scheme.etalePrecoverage_le_fppfPrecoverage

/-- The scheme-level property that every quasi-compact open has finitely many irreducible
components is local for the smooth precoverage. -/
instance isLocalSmooth :
    CategoryTheory.ObjectProperty.IsLocal
      (fun U : Scheme.{u} ↦ Scheme.HasFiniteIrreducibleComponentsOnCompactOpens U)
      Scheme.bigSmoothPrecoverage :=
  CategoryTheory.ObjectProperty.IsLocal.of_le Scheme.bigSmoothPrecoverage_le_fppfPrecoverage

end AlgebraicGeometry.Scheme.HasFiniteIrreducibleComponentsOnCompactOpens
