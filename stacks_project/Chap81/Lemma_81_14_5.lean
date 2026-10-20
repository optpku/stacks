/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.SchemeTheoreticImage.StrictTransform

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/- Lemma 81.14.5: let `S` be a scheme, let `X ⟶ B` and `Y ⟶ B` be morphisms of
algebraic spaces over `S`, let `U ⊂ X` be an open subspace, and let
`q : V ⟶ X ×_B Y` be a quasi-compact morphism whose composition with the first
projection maps into `U`. If `b : X' ⟶ X` is a `U`-admissible blowup with
center `center`, then the scheme-theoretic image of the induced morphism
`V ⟶ X' ×_B Y` and the strict transform of the scheme-theoretic image of `q`
have the same canonical ideal subobject in `X' ×_B Y`. -/
@[stacks 0F49] #check
  (AlgebraicGeometry.AlgebraicSpace.image_liftAdmissible_isomorphic_strictTransform :
    ∀ {S : Scheme.{u}} {B X Y V X' : AlgebraicSpace S}
    (f : X ⟶ B) (g : Y ⟶ B) (q : V ⟶ pullback f g) [QuasiCompact q]
    (U : OpenSubspace X) (b : X' ⟶ X) (center : ClosedSubspace X)
    (hb : IsAdmissibleBlowupCenter U b center)
    (qU : V ⟶ U.X) (hqU : qU ≫ U.ι = q ≫ pullback.fst f g),
    Hom.idealSheafSubobject (liftAdmissiblePullback f g q U b qU
        (isIso_pullbackFst_of_isAdmissibleBlowupCenter U b center hb) hqU) =
      Hom.idealSheafSubobject (strictTransformImageMap f g q b center hb.isBlowup))

end AlgebraicGeometry.AlgebraicSpace
