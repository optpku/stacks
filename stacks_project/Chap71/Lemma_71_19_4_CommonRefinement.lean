module

public import stacks_project.Chap71.Lemma_71_19_3_AdmissibleBlowup
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Blowup.CommonRefinement

/-!
# Common refinements of admissible blowups of algebraic spaces

A finite family of admissible blowups of a quasi-compact and quasi-separated
algebraic space has a common admissible refinement whose comparison morphisms
are themselves admissible blowups.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace

universe u

#check (AlgebraicGeometry.AlgebraicSpace.OpenSubspace.inverseImage :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S},
    OpenSubspace X → (Y ⟶ X) → OpenSubspace Y)
