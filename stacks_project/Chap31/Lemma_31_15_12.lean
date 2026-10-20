/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.AlgebraicGeometry.Scheme.Divisor.EffectiveCartier.Presentation
import StacksCheckRecall

universe u

/- Lemma 31.15.12 (1): on a Noetherian scheme admitting an ample invertible module, every
invertible module is isomorphic to the difference sheaf of two effective Cartier divisors that
avoid any prescribed finite subset. -/
@[stacks 0AYM] #check
  (AlgebraicGeometry.Scheme.Modules.Invertible.exists_iso_differenceSheaf_avoiding_of_hasAmpleInvertibleModule :
    ∀ {X : AlgebraicGeometry.Scheme.{u}} [AlgebraicGeometry.IsNoetherian X],
      AlgebraicGeometry.Scheme.Modules.HasAmpleInvertibleModule X →
        ∀ (L : X.Modules) [AlgebraicGeometry.Scheme.Modules.Invertible L]
          (E : Set X), E.Finite →
          ∃ (D : X.IdealSheafData)
            (hD : AlgebraicGeometry.IsEffectiveCartierDivisor D.subschemeι)
            (D' : X.IdealSheafData)
            (hD' : AlgebraicGeometry.IsEffectiveCartierDivisor D'.subschemeι),
            Disjoint E (D.support : Set X) ∧
              Disjoint E (D'.support : Set X) ∧
                Nonempty
                  (L ≅ @AlgebraicGeometry.Scheme.IdealSheafData.differenceSheaf
                    X D D' hD hD'))

/- Lemma 31.15.12 (2): if the scheme is also quasi-affine, the denominator divisor may be
chosen empty, so the invertible module is the associated sheaf of one effective Cartier divisor
avoiding the prescribed finite subset. -/
@[stacks 0AYM] #check
  (AlgebraicGeometry.Scheme.Modules.Invertible.exists_iso_associatedSheaf_avoiding_of_isQuasiAffine :
    ∀ {X : AlgebraicGeometry.Scheme.{u}} [AlgebraicGeometry.IsNoetherian X]
      [X.IsQuasiAffine],
      AlgebraicGeometry.Scheme.Modules.HasAmpleInvertibleModule X →
        ∀ (L : X.Modules) [AlgebraicGeometry.Scheme.Modules.Invertible L]
          (E : Set X), E.Finite →
          ∃ (D : X.IdealSheafData)
            (hD : AlgebraicGeometry.IsEffectiveCartierDivisor D.subschemeι),
            Disjoint E (D.support : Set X) ∧
              Nonempty
                (L ≅ @AlgebraicGeometry.Scheme.IdealSheafData.associatedSheaf X D hD))
