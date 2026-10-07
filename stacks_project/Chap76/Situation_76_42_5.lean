module

import StacksCheckRecall
public import Mathlib.AlgebraicGeometry.Spec
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.Noetherian.Defs
public import stacks_project.Chap65.Lemma_65_6_2_OfOver
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation
public import stacks_project.Chap67.Definition_67_14_4_IdealSubobject
public import stacks_project.Chap67.Definition_67_40_1_FiniteType
public import stacks_project.Chap67.Lemma_67_24_2_FieldPoints
public import stacks_project.Chap69.Lemma_69_22_2_IdealPower

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules.IdealPowerCohomology

universe u

section

variable (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A)
  [IsAdicComplete I A] (X : AlgebraicSpace (Spec (CommRingCat.of A)))
  [FiniteType (toBase X)] [Separated (toBase X)]

/- Situation 76.42.5: A is a Noetherian ring complete with respect to an ideal I,
f : X ⟶ Spec A is a finite type separated morphism of algebraic spaces, and
𝓘 = I𝒪_X is the inverse-image ideal along toBase X. -/
@[stacks 08B7] #check
  (AlgebraicGeometry.AlgebraicSpace.Separated :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S}, (X ⟶ Y) → Prop)

/- The coefficient ring is Noetherian. -/
#check (IsNoetherianRing A : Prop)

/- The coefficient ring is complete for the I-adic topology. -/
#check (IsAdicComplete I A : Prop)

/- The structure morphism toBase X is of finite type. -/
#check (AlgebraicGeometry.AlgebraicSpace.FiniteType (toBase X) : Prop)

/- The ideal I𝒪_X is the pullback ideal along toBase X. -/
#check
  (AlgebraicGeometry.AlgebraicSpace.Modules.IdealPowerCohomology.pullbackIdeal I
    (toBase X) : IdealSubobject X)

end
