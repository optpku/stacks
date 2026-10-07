module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Smooth.Slicing

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom

/- Lemma 37.38.2: if `f` is smooth at `x` and the canonical Kähler-differential
base-change map from the fibre stalk to `κ(x)` has nontrivial kernel, then an
affine neighbourhood of `x` contains an effective Cartier divisor through `x`
whose morphism to the base is smooth. -/
@[stacks 057D] #check
  (AlgebraicGeometry.Scheme.Hom.SmoothAt.exists_smoothEffectiveCartierDivisor :
    ∀ {X S : Scheme.{u}} {f : X ⟶ S} {x : X},
      f.SmoothAt x →
      (¬ Function.Injective
        (KaehlerDifferential.mapBaseChange
          (S.residueField (f x)) (fiberStalkAt f x) (X.residueField x))) →
      ∃ U : X.affineOpens,
        ∃ hxU : x ∈ (U : X.Opens),
          ∃ D : (U : X.Opens).toScheme.IdealSheafData,
            ⟨x, hxU⟩ ∈ D.support ∧
              IsEffectiveCartierDivisor D.subschemeι ∧
              Smooth (D.subschemeι ≫ ((U : X.Opens).ι ≫ f)))

end AlgebraicGeometry.Scheme.Hom
