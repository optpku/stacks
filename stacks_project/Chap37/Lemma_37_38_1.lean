/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Smooth.Slicing

@[expose] public section

open CategoryTheory
open AlgebraicGeometry
open scoped AlgebraicGeometry nonZeroDivisors TensorProduct

universe u

namespace AlgebraicGeometry.Scheme.Hom

/- Lemma 37.38.1: a germ in the maximal ideal whose relative differential is
nonzero at a smooth point extends to a principal effective Cartier divisor on
an affine neighbourhood that is smooth over the base. -/
@[stacks 057C] #check
  (AlgebraicGeometry.Scheme.Hom.SmoothAt.exists_affineOpen_smoothEffectiveCartierDivisor :
    ∀ {X S : Scheme.{u}} {f : X ⟶ S} {x : X}
    (hf : f.SmoothAt x) (h : X.presheaf.stalk x)
    (hmax : h ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk x))
    (hdiff : (1 : X.residueField x) ⊗ₜ[X.presheaf.stalk x]
      (CommRingCat.KaehlerDifferential.d h :
        CommRingCat.KaehlerDifferential (f.stalkMap x)) ≠ 0),
    ∃ U : X.affineOpens,
      ∃ hxU : x ∈ (U : X.Opens),
        ∃ hU : Γ(X, (U : X.Opens)),
          X.presheaf.germ (U : X.Opens) x hxU hU = h ∧
            let D : (U : X.Opens).toScheme.IdealSheafData :=
              Scheme.IdealSheafData.ofIdealTop
                (Ideal.span ({(U : X.Opens).topIso.inv hU} : Set (Γ((U : X.Opens), ⊤))))
            (⟨x, hxU⟩ ∈ D.support ∧
              IsRelativeEffectiveCartierDivisor ((U : X.Opens).ι ≫ f) D ∧
              Smooth (D.subschemeι ≫ ((U : X.Opens).ι ≫ f))))

end AlgebraicGeometry.Scheme.Hom
