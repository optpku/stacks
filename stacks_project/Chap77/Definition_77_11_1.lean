module

public import stacks_project.Chap77.Definition_77_11_1_Universal
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory

universe u

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
variable (ℱ : X.Modules) [ℱ.IsQuasicoherent]

/- Definition 77.11.1 (1): the universal flattening of a quasi-coherent `𝒪_X`-module `ℱ`
exists when the flattening functor `F_flat` of Situation 77.7.8, viewed as a functor
`(Sch/S)ᵒᵖ ⥤ Type`, is an algebraic space. -/
@[stacks 0CWR] #check
  (Modules.Flattening.HasUniversalFlattening f ℱ : Prop)

/- Definition 77.11.1 (2): the universal flattening of `X` exists when the universal
flattening of `𝒪_X` exists. -/
@[stacks 0CWR] #check
  (HasUniversalFlattening f : Prop)
