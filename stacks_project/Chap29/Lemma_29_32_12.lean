module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.Scheme.Differentials.FiniteType

open CategoryTheory
open scoped AlgebraicGeometry

universe u

/- Lemma 29.32.12: for a locally finite type morphism of schemes `f : X ⟶ S`, the relative
differential sheaf `Ω[f.toShHom]` is a finite-type `𝒪_X`-module. -/
@[stacks 01V2] #check
  (AlgebraicGeometry.isFiniteType_differentials_of_locallyOfFiniteType :
    ∀ {X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S)
      [AlgebraicGeometry.LocallyOfFiniteType f],
      (Ω[f.toShHom]).IsFiniteType)
