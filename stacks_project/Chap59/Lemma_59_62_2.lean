module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.BrauerGroup.Exponent

@[expose] public section

open CategoryTheory
open AlgebraicGeometry
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.Modules

universe u

/- Lemma 59.62.2: the Brauer class of an Azumaya algebra locally free of rank `d ^ 2`
is annihilated by `d`. -/
@[stacks 0A2L] #check (AlgebraicGeometry.Scheme.classOf_pow_eq_one :
  ∀ {S : Scheme.{u}} (A : S.Modules) [MonObj A] [IsAzumaya A] (d : ℕ)
    [IsFiniteLocallyFreeOfRank (d ^ 2) A], classOf A ^ d = 1)
