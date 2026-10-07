module

public import stacks_project.Chap87.Definition_87_9_1_SetTheoretic
public import stacks_project.Chap87.Definition_87_9_1_Affine
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u v

/- Definition 87.9.1 (1): a sheaf `X` on `(Sch/S)_fppf` is an affine formal algebraic
space when it is isomorphic, as an fppf sheaf, to a directed colimit of affine
objects along thickening transitions, and it satisfies the set-theoretic condition
that there exist objects `U`, `R` of the same fixed site with fppf-sheaf
surjections `U ⟶ X` and `R ⟶ U ×_X U`. -/
@[stacks 0AI7] #check IsAffineFormalAlgebraicSpace

/- Definition 87.9.1 (2): a morphism of affine formal algebraic spaces over `S` is a
map of sheaves. -/
@[stacks 0AI7] #check
  ∀ {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X Y : Sheaf (𝒮.bigTopology S) (Type (max u v)))
    [IsAffineFormalAlgebraicSpace X] [IsAffineFormalAlgebraicSpace Y],
    X ⟶ Y
