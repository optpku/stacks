module

public import ReasLib.AlgebraicGeometry.Scheme.QuasiAffine.Immersion
import StacksCheckRecall

/-!
# Lemma 28.27.2

Quasi-affineness is preserved by quasi-compact immersions.

@stack 0BCK
-/

@[expose] public section

open AlgebraicGeometry

universe u

/- Lemma 28.27.2: A quasi-compact immersion into a quasi-affine scheme has
quasi-affine source. -/
@[stacks 0BCK] #check
  (AlgebraicGeometry.Scheme.IsQuasiAffine.of_isImmersion_of_quasiCompact :
    ∀ {X X' : Scheme.{u}} {i : X' ⟶ X},
      X.IsQuasiAffine → IsImmersion i → QuasiCompact i → X'.IsQuasiAffine)
