module

public import ReasLib.AlgebraicGeometry.Scheme.Noetherian.Etale
public import ReasLib.AlgebraicGeometry.Scheme.Jacobson.Etale
public import ReasLib.AlgebraicGeometry.Scheme.SerreCondition.Etale
public import ReasLib.AlgebraicGeometry.Scheme.CohenMacaulay.Etale
public import ReasLib.AlgebraicGeometry.Scheme.Gorenstein.Etale
public import ReasLib.AlgebraicGeometry.Scheme.Reduced.Etale
public import ReasLib.AlgebraicGeometry.Scheme.Normal.Etale
public import ReasLib.AlgebraicGeometry.Scheme.Regular.Etale
public import ReasLib.AlgebraicGeometry.Scheme.Normal.Nagata.Etale

/-!
# Étale-locality of scheme properties

These scheme properties are local for the étale precoverage.
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry

#check (AlgebraicGeometry.IsLocallyNoetherian.isLocalEtale :
  ObjectProperty.IsLocal
    (IsLocallyNoetherian : ObjectProperty Scheme.{u}) Scheme.etalePrecoverage)
