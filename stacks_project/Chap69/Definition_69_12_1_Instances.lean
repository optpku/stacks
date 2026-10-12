/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap66.Definition_66_29_1_RingedSite

/-!
# Double-slice sheafification on the small étale site

`SheafOfModules.IsCoherent` needs weak sheafification on over-over slices. The small étale
topology of an algebraic space already has the one-slice instances; these record the
double-slice counterparts.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Abelian-group-valued weak sheafification exists on every double slice of the small étale
topology of an algebraic space. -/
instance smallEtaleTopology_over_over_hasWeakSheafify {S : Scheme.{u}}
    (X : AlgebraicSpace S) :
    ∀ (U : smallEtaleSite X) (V : Over U),
      HasWeakSheafify (((smallEtaleTopology X).over U).over V) AddCommGrpCat.{u} :=
  sorry

/-- On every double slice of the small étale topology of an algebraic space, sheafification
equivalences are the locally bijective morphisms. -/
instance smallEtaleTopology_over_over_wEqualsLocallyBijective {S : Scheme.{u}}
    (X : AlgebraicSpace S) :
    ∀ (U : smallEtaleSite X) (V : Over U),
      (((smallEtaleTopology X).over U).over V).WEqualsLocallyBijective AddCommGrpCat.{u} :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
