module

public import stacks_project.Chap106.Lemma_106_6_8_Inertia
public import stacks_project.Chap106.Lemma_106_6_8_Module

/-!
# Automorphism sheaves of first-order lifts are abelian and quasi-coherent

In the gerbe of lifts along a first-order thickening, automorphism sheaves of
objects are abelian, and the band of Lemma 8.11.8 is a quasi-coherent
`O_W`-module, identified étale-locally with the Hom-parameter module of each
lift.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicStack
open AlgebraicGeometry.AlgebraicSpace
open Functor.IsFibered.InGroupoids
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack.Lift

variable {S : Scheme.{u}} {X X' : GroupoidsOver S}
variable [AlgebraicStack X] [AlgebraicStack X']
variable (iX : X ⟶ X') [IsThickening iX]
variable {W : AlgebraicSpace S} (x : W.toGroupoids ⟶ X)
variable [Groupoids.Hom.Smooth x]

/-- Lemma 106.6.8 (1): in the gerbe of lifts `p : C ⥤ W_spaces,étale` of
Remark 106.6.1, if `X ⊂ X'` is a first-order thickening, then the
automorphism sheaves of objects are abelian. -/
@[stacks 0CKG]
instance instAutomorphismIsAbelian [IsFirstOrderThickening iX] :
    Automorphism.IsAbelian (p iX x) :=
  sorry

/-- Lemma 106.6.8 (2): the sheaf of groups `G` constructed in Lemma 8.11.8 is a
quasi-coherent `O_W`-module. -/
@[stacks 0CKG]
instance instBandChoiceModuleIsQuasicoherent [IsFirstOrderThickening iX] :
    (bandChoiceModule iX x).IsQuasicoherent :=
  sorry

end AlgebraicGeometry.AlgebraicStack.Lift
