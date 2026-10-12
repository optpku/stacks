/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap65.Lemma_65_11_1_OfEtaleSurjective
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits MorphismProperty

universe u

variable {S : Scheme.{u}} {F : (Over S)ᵒᵖ ⥤ Type u}
variable (hF : Presheaf.IsSheaf (Scheme.fppfTopology.over S) F)
variable {U : Over S} (p : yoneda.obj U ⟶ F)
variable (hp : (over (@Etale ⊓ @Surjective)).presheaf p)

/- Lemma 65.11.1: let `S` be a scheme contained in `Sch_fppf`. Let `F` be a sheaf
on `(Sch/S)_fppf` such that there exists `U` in `Ob((Sch/S)_fppf)` and a map
`U ⟶ F` which is representable, surjective, and étale. Then `F` is an algebraic
space. -/
@[stacks 0BGQ] #check (AlgebraicSpace.ofEtaleSurjective hF p hp : AlgebraicSpace S)
