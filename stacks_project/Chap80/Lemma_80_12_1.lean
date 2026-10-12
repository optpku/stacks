/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap80.Lemma_80_12_1_OfEtaleSheaf
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits MorphismProperty

universe u

variable {S : Scheme.{u}} {F : (Over S)ᵒᵖ ⥤ Type u}
variable (hF : Presheaf.IsSheaf (Scheme.etaleTopology.over S) F)
variable (hΔ : yoneda.relativelyRepresentable (Limits.diag F))
variable {U : Over S} (p : yoneda.obj U ⟶ F)
variable (hp : (over (@Etale ⊓ @Surjective)).presheaf p)

/- Lemma 80.12.1: denote the common underlying category of `Sch_fppf` and
`Sch_étale` by `Sch_α` (see Topologies, Remark 34.11.1), recovered here as the
common `Over S` of `Scheme.etaleTopology` and `Scheme.fppfTopology`. Let `S` be a
scheme. Let `F : (Over S)ᵒᵖ ⥤ Type` be a presheaf that is a sheaf for the étale
topology, whose diagonal `Δ : F ⟶ F ⨯ F` is representable, and that admits `U`
over `S` with a map `U ⟶ F` which is surjective and étale. Then `F` is an
algebraic space in the sense of Algebraic Spaces, Definition 65.6.1. -/
@[stacks 076M] #check (AlgebraicSpace.ofEtaleSheaf hF hΔ p hp : AlgebraicSpace S)
