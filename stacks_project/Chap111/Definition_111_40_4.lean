/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import ReasLib.AlgebraicGeometry.Scheme.Module.FiniteLocallyFree.Rank
public import ReasLib.RingTheory.PicardGroup.Invertible
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules
open CategoryTheory
open CategoryTheory.MonoidalCategory

universe u

section

variable {R : CommRingCat.{u}} (M : ModuleCat.{u} R)

/- Definition 111.40.4 (1): an `R`-module `M` is invertible if `tilde M` is an invertible sheaf
on `Spec R`. -/
@[stacks 02AG]
#check (IsFiniteLocallyFreeOfRank 1 (tilde M) : Prop)

end

section

variable {R : Type u} [CommRing R] (M : ModuleCat R)

/- Definition 111.40.4 (2): an `R`-module `M` is trivial if it is isomorphic to `R` as an
`R`-module. -/
@[stacks 02AG]
#check (isUnitObject M : Prop)

#check (ModuleCat.isUnitObject_iff_linearEquiv M :
    isUnitObject M ↔ Nonempty (M ≃ₗ[R] R))

end

#check @Module.Invertible
#check @Module.Invertible.iff_finiteLocallyFreeOfRank_one
#check AlgebraicGeometry.tildeSelf
