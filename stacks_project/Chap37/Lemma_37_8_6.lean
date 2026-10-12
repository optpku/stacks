/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FormallyEtale.UniversalFirstOrder
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

/- Lemma 37.8.6: formal étaleness is equivalent to formal unramifiedness together
with triviality of a universal first-order thickening, to formal unramifiedness together
with vanishing conormal sheaf, and to simultaneous vanishing of relative differentials
and the conormal sheaf. -/
@[stacks 04FE] #check
  (AlgebraicGeometry.FormallyEtale.tfae_universalFirstOrder :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S)
      (T : Thickening.Over S) (hleft : T.left = Over.mk f)
      [Thickening.IsUniversalFirstOrder T],
      let i := (Over.forget S).map T.hom
      let C := Scheme.Hom.conormalSheaf i
      List.TFAE [
        FormallyEtale f,
        FormallyUnramified f ∧ IsIso i,
        FormallyUnramified f ∧ Limits.IsZero C,
        Limits.IsZero Ω[f.toShHom] ∧ Limits.IsZero C])
