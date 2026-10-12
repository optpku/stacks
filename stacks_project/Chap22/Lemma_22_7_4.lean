/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.DifferentialGradedModule.Admissible.Factorization
import StacksCheckRecall

@[expose] public section

open CategoryTheory DifferentialGradedModule
open DifferentialGradedModule.SplitMonoFactorization

universe u v w

variable {R : Type u} [CommRing R]
variable {A : CochainDGAlgebra.{u, v} R}
variable {K L : DifferentialGradedModule.{u, w} A}
variable (alpha : K ⟶ L)

/- Lemma 22.7.4 (1) (09JW): the canonical inclusion into
`L ⊞ mappingCone (𝟙 K)` followed by projection is the original map. -/
@[stacks 09JW] #check
  (inclusion_comp_projection alpha :
    inclusion alpha ≫ projection K L = alpha)

/- Lemma 22.7.4 (2) (09JW): the canonical inclusion is admissibly monic. -/
@[stacks 09JW] #check
  (isAdmissibleMono_inclusion alpha : IsAdmissibleMono (inclusion alpha))

/- Lemma 22.7.4 (3) (09JW): the target inclusion is a section of the projection. -/
@[stacks 09JW] #check
  (section_comp_projection K L : section_ K L ≫ projection K L = 𝟙 L)

/- Lemma 22.7.4 (4) (09JW): projection followed by its section is homotopic to the
identity of the factorization object. -/
@[stacks 09JW] #check
  (projectionHomotopy K L :
    Homotopy (projection K L ≫ section_ K L) (𝟙 (obj K L)))

/- The construction supplies explicit graded retraction data and a reusable morphism-property
view of the projection. -/
#check (retraction K L : Graded.Hom (obj K L).toGraded K.toGraded)
#check (homotopyEquivalences_projection K L : homotopyEquivalences A (projection K L))
