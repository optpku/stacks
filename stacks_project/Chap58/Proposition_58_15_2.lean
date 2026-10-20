module

public import ReasLib.AlgebraicGeometry.Scheme.FundamentalGroup.HomotopyExactSequence
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {X S : Scheme.{u}}

/- Proposition 58.15.2 -/
@[stacks 0C0J]
#check (@AlgebraicGeometry.Scheme.Hom.homotopyExactSequence :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S) [Flat f] [IsProper f]
    [Scheme.Hom.FinitePresentation f]
    [GeometricallyConnected f] [GeometricallyReduced f] [ConnectedSpace S]
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (sbar : Spec (.of Ω) ⟶ S) (xbar : Spec (.of Ω) ⟶ pullback f sbar)
    (hpoint : xbar ≫ pullback.snd f sbar = 𝟙 (Spec (.of Ω))),
    Function.MulExact (fundamentalGroupMap (pullback.fst f sbar) xbar)
      (fundamentalGroupMap f (xbar ≫ pullback.fst f sbar)) ∧
    Function.Surjective (fundamentalGroupMap f (xbar ≫ pullback.fst f sbar)))

end AlgebraicGeometry.Scheme.Hom
