/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap97.Lemma_97_11_1_Sheaf
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.RestrictionOfScalars

universe u

variable {S : Scheme.{u}} {X Z B T : AlgebraicSpace S} (f : X ⟶ Z) (g : Z ⟶ B)

/- Lemma 97.11.1 (1): `Res_{Z/B}(X)` is a sheaf on `(Sch/S)_fppf`. -/
@[stacks 05YB]
#check (restrictionOfScalars_isSheaf f g :
    Presheaf.IsSheaf (Scheme.fppfTopology.over S) (restrictionOfScalars f g))

/- Lemma 97.11.1 (2): for an algebraic space `T` over `S`, sheaf morphisms
`T ⟶ Res_{Z/B}(X)` correspond canonically to pairs `(a, b)` as in (05Y9). -/
@[stacks 05YB]
#check (RestrictionOfScalars.homEquiv f g :
    (uliftSheaf T ⟶ restrictionOfScalarsSheaf f g) ≃ RestrictScalars.Pair f g T)
