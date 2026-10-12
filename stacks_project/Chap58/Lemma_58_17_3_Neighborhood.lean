/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.FiniteEtale.Neighborhood

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

variable {X : Scheme.{u}} [IsNoetherian X]

#check (openNhdsAsOpen : (I : X.IdealSheafData) →
  (CoherentCompletion.compactSupport I).openNhds → X.Opens)
#check (openNhdsScheme : (I : X.IdealSheafData) →
  (CoherentCompletion.compactSupport I).openNhds → Scheme.{u})
#check (openNhdsι : (I : X.IdealSheafData) →
  (V : (CoherentCompletion.compactSupport I).openNhds) → openNhdsScheme I V ⟶ X)
#check (closedSubschemeιOnOpen : (I : X.IdealSheafData) →
  (V : (CoherentCompletion.compactSupport I).openNhds) →
    I.subscheme ⟶ openNhdsScheme I V)
#check (finiteEtaleNeighborhoodDiagram : (I : X.IdealSheafData) →
  (CoherentCompletion.compactSupport I).openNhdsᵒᵖ ⥤ Cat)
#check (finiteEtaleNeighborhoodRestrictionCocone : (I : X.IdealSheafData) →
  Cocone (finiteEtaleNeighborhoodDiagram I))
#check (finiteEtaleNeighborhoodRestriction : (I : X.IdealSheafData) →
  (t : ColimitCocone (finiteEtaleNeighborhoodDiagram I)) →
    t.cocone.pt ⥤ Cat.of (FiniteEtale I.subscheme))

end AlgebraicGeometry.Scheme
