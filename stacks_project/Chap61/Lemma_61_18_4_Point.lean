/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.GeometricPoint.ProEtale

/-!
# Points of the small pro-étale site

A geometric point of `S` determines a point of the small pro-étale site `S.ProEt`,
whose fibre is the coyoneda fibre of the structure morphism. Stalks of
presheaves are the corresponding presheaf fibres.
-/

open CategoryTheory Opposite
open AlgebraicGeometry

universe u

@[expose] public section

/- The reusable declarations are owned by the ReasLib pro-étale point module.
The typed checks below preserve this source-facing module as an importable bridge. -/
#check (AlgebraicGeometry.Scheme.GeometricPoint.ProetaleNeighborhood :
    ∀ {S : Scheme.{u}} (s : Scheme.GeometricPoint S), Type (u + 1))
#check (AlgebraicGeometry.Scheme.GeometricPoint.toSmallProetalePoint :
    ∀ {S : Scheme.{u}} (s : Scheme.GeometricPoint S),
      (AlgebraicGeometry.Scheme.ProEt.topology S).Point)
#check (AlgebraicGeometry.Scheme.ProEt.stalk :
    ∀ {S : Scheme.{u}} (s : Scheme.GeometricPoint S)
      (F : S.ProEtᵒᵖ ⥤ Type u), Type u)
