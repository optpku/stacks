module

public import stacks_project.Chap92.«92_28_0_1_Transitivity»
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Cotangent

universe u

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)

/- Definition 92.26.1: Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of algebraic
spaces over `S`. The cotangent complex `L_{X/Y}` of `X` over `Y` is the cotangent
complex of the morphism of ringed topoi `f_small` between the small étale sites of
`X` and `Y` (see Properties of Spaces, Lemma 66.21.3 and Definition 92.22.1). -/
@[stacks 08VD]
#check (cotangentCochain f : CochainComplex (CommModules X) ℤ)

#check (cotangent f : DerivedCategory (CommModules X))
#check cotangentCochain_eq
#check (ringedToposHom f : RingedSite.ToposHom (ringedSite X) (ringedSite Y))
#check structureMapLift
#check commInverseImageStructureSheafMap_forget
