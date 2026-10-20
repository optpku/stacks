module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.DescentConditions
import StacksCheckRecall

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry CategoryTheory.ObjectProperty

namespace AlgebraicGeometry.AlgebraicSpace

/- Remark 68.6.3: reasonable algebraic spaces are technically easier to work with
than very reasonable ones. If `f : X ⟶ Y` is a quasi-compact étale surjective
morphism of algebraic spaces and `X` is reasonable, then so is `Y`. Descent of
the property “very reasonable” along such a morphism is not claimed. -/
@[stacks 03JY] #check
  (AlgebraicGeometry.AlgebraicSpace.IsReasonable.of_quasiCompact_etale_surjective :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y),
      [QuasiCompact f] → [Etale f] → [Surjective f] → [IsReasonable X] → IsReasonable Y)

end AlgebraicGeometry.AlgebraicSpace
