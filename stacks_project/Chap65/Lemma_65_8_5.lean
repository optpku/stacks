module

public import stacks_project.Chap65.Lemma_65_8_5_OpenCover
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits MorphismProperty

universe u v

variable {S : Scheme.{u}} {I : Type v} [Small.{u} I] {F : (Over S)ᵒᵖ ⥤ Type u}
variable (hF : Presheaf.IsSheaf (Scheme.fppfTopology.over S) F)
variable {X : I → AlgebraicSpace S} (ι : ∀ i, (X i).functorOfPoints ⟶ F)
variable (h_open : ∀ i, (over (@IsOpenImmersion)).presheaf (ι i))
variable (h_surj : Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S)
    (AlgebraicSpace.openCoverDesc X ι))

/- Lemma 65.8.5: let `S` be a scheme contained in `Sch_fppf`. Let `F` be a presheaf
of sets on `(Sch/S)_fppf`. Assume `F` is a sheaf, and that there is a not-too-large
index type `I` together with algebraic spaces `X i` over `S` and inclusions
`ι i : (X i).functorOfPoints ⟶ F` that are representable open immersions
(Definition 65.5.1), such that `openCoverDesc X ι : ∐ (X i).functorOfPoints ⟶ F`
is surjective as a map of sheaves and `∐ X i` is an algebraic space (`[Small.{u} I]`,
Lemma 65.8.4). Then `F` is an algebraic space. -/
@[stacks 02WR] #check (AlgebraicSpace.ofOpenCover hF ι h_open h_surj : AlgebraicSpace S)
