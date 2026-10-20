module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.H.Presentation

/-!
# Compatibility bridge for chosen presentations of big h sites

The reusable h-site presentation API is owned by
`ReasLib.AlgebraicGeometry.Scheme.Sites.H.Presentation`.
-/

@[expose] public section

open CategoryTheory

universe u v

#check (AlgebraicGeometry.Scheme.hPrecoverage :
  Precoverage AlgebraicGeometry.Scheme.{u})

#check (AlgebraicGeometry.ChosenBigHSite.{u, v} :
  Type (max (u + 1) (v + 1)))
