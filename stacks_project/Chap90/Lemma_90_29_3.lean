module

public import ReasLib.AlgebraicGeometry.FormalDeformation.ArtinianLocal.ResidueChange.Tangent
import StacksCheckRecall

/-!
# Lemma 90.29.3

In Situation 90.29.1, if `p` is a predeformation category whose associated
isomorphism-class functor satisfies (S2), there is a canonical bijective
`l`-linear comparison `T p ⊗[k] l ⟶ T(p_{l/k})` of tangent spaces.
-/

@[expose] public section

noncomputable section

open CategoryTheory hiding Linear
open CategoryTheory.Functor
open ArtinianLocalAlgCat
open scoped TensorProduct

universe u v w

variable (Λ k l : Type u) [CommRing Λ] [IsNoetherianRing Λ]
  [Field k] [Algebra Λ k] [Module.Finite Λ k]
  [Field l] [Algebra Λ l] [Module.Finite Λ l]
  [Algebra k l] [IsScalarTower Λ k l] [Module.Finite k l]
variable {F : Type v} [Category.{w} F] (p : F ⥤ ArtinianLocalAlgCat Λ k)
variable [IsPredeformationCategory p] [HasSchlessingerH2 (fiberIsoClassFunctor p)]

/- Lemma 90.29.3: The canonical tangent comparison after finite residue-field
change is an isomorphism of `l`-vector spaces. -/
@[stacks 07WB]
#check (ArtinianLocalAlgCat.residueChangeOver.bijective_tangentSpaceTensor Λ k l p :
  Function.Bijective (ArtinianLocalAlgCat.residueChangeOver.tangentSpaceTensor Λ k l p))
