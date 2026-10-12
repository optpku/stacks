/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap76.Lemma_76_7_11_Retraction
public import stacks_project.Chap76.Lemma_76_7_11_Splitting
import StacksCheckRecall

/-!
# Split exactness of the conormal sequence of an immersion of algebraic spaces

An immersion of algebraic spaces over a base that (étale locally) has a left
inverse has a (étale locally) split-exact conormal sequence.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Hom
open AlgebraicGeometry.AlgebraicSpace.Hom.Conormal.Differentials

noncomputable section

universe u

variable {S : Scheme.{u}}
variable {B X Z : AlgebraicSpace S}
variable (i : Z ⟶ X) [IsImmersion i] (f : X ⟶ B)

/- Lemma 76.7.11: Let `S` be a scheme. Let `B` be an algebraic space over `S`.
Let `i : Z ⟶ X` be an immersion of algebraic spaces over `B`, and assume `i`
(étale locally) has a left inverse. Then the canonical sequence
`0 ⟶ C_{Z/X} ⟶ i^* Ω_{X/B} ⟶ Ω_{Z/B} ⟶ 0` of Lemma 76.7.10 is (étale locally)
split exact. If `r : X ⟶ Z` is a left inverse over `B`, the splitting section
of `i^* Ω_{X/B} ⟶ Ω_{Z/B}` is `i^* c_r`. -/
@[stacks 05ZB] #check (etaleLocallySplit_of_etaleLocallyHasRetraction i f :
  EtaleLocallyHasRetractionOver i f → IsEtaleLocallySplit i f)

/- A global left inverse over `B` splits the canonical conormal complex. -/
@[stacks 05ZB] #check (complex_splitting_of_hasRetraction i f :
  HasRetractionOver i f → Nonempty ((complex i f).Splitting))

/- The source-named section `i^* c_r` of `i^* Ω_{X/B} ⟶ Ω_{Z/B}`. -/
@[stacks 05ZB] #check (sectionOfRetraction i f :
  ∀ (r : X ⟶ Z), i ≫ r = 𝟙 Z → r ≫ i ≫ f = f →
    (relativeDifferentials (i ≫ f) ⟶
      (Modules.pullback i).obj (relativeDifferentials f)))
