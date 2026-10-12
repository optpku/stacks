/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap65.Lemma_65_11_2_OfEtaleSurjectiveSpace
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits MorphismProperty

universe u

variable {S : Scheme.{u}} {G : AlgebraicSpace S} {F : (Over S)ᵒᵖ ⥤ Type u}
variable (hF : Presheaf.IsSheaf (Scheme.fppfTopology.over S) F)
variable (a : G.functorOfPoints ⟶ F)
variable (ha : (over (@Etale ⊓ @Surjective)).presheaf a)

/- Lemma 65.11.2: let `S` be a scheme contained in `Sch_fppf`. Let `G` be an
algebraic space over `S`, let `F` be a sheaf on `(Sch/S)_fppf`, and let
`G ⟶ F` be a representable transformation of functors which is surjective
and étale. Then `F` is an algebraic space. -/
@[stacks 0BGR] #check (AlgebraicSpace.ofEtaleSurjectiveSpace hF a ha : AlgebraicSpace S)
