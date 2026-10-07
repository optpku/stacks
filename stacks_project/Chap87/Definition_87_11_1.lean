module

public import stacks_project.Chap87.Definition_87_11_1_Representable
public import stacks_project.Chap87.Definition_87_11_1_Formal
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u v

/- Definition 87.11.1 (1): a sheaf `X` on `(Sch/S)_fppf` is a formal algebraic
space when there exist sheaf maps `X_ i ⟶ X` with each `X_ i` an affine formal
algebraic space, each `X_ i ⟶ X` representable by algebraic spaces and étale,
the coproduct map `∐ X_ i ⟶ X` surjective as a map of sheaves, and `X`
satisfying the set-theoretic condition that there exist objects `U`, `R` of
the same fixed site with fppf-sheaf surjections `U ⟶ X` and `R ⟶ U ×_X U`. -/
@[stacks 0AIM] #check IsFormalAlgebraicSpace

/- Definition 87.11.1 (2): a morphism of formal algebraic spaces over `S` is a
map of sheaves. -/
@[stacks 0AIM] #check
  ∀ {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X Y : Sheaf (𝒮.bigTopology S) (Type (max u v)))
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y],
    X ⟶ Y
