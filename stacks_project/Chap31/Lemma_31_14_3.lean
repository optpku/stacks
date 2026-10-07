module

import ReasLib.AlgebraicGeometry.Scheme.Divisor.EffectiveCartier.Sum.Restriction
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme.Modules

noncomputable section

universe u

/- Lemma 31.14.3: if `D ⊆ D'` are effective Cartier divisors on `X` and `D' = D + C`,
then the restriction of `D.negSheaf` to `C`, the structure sheaf of `D'`, and the structure
sheaf of `D` form a short exact sequence after pushforward to `X`. -/
@[stacks 0C4T] #check
  (AlgebraicGeometry.Scheme.IdealSheafData.exists_negSheaf_restriction_shortExact_of_eq_sum :
    ∀ {X : Scheme.{u}} (D D' C : X.IdealSheafData)
      [IsEffectiveCartierDivisor D.subschemeι]
      [IsEffectiveCartierDivisor D'.subschemeι]
      [IsEffectiveCartierDivisor C.subschemeι],
      D' ≤ D → D' = effectiveCartierDivisorSum D C →
        ∃ (f :
            (Scheme.Modules.pushforward C.subschemeι).obj
                ((Scheme.Modules.pullback C.subschemeι).obj D.negSheaf) ⟶
              (Scheme.Modules.pushforward D'.subschemeι).obj
                (SheafOfModules.unit D'.subscheme.ringCatSheaf : D'.subscheme.Modules))
          (g :
            (Scheme.Modules.pushforward D'.subschemeι).obj
                (SheafOfModules.unit D'.subscheme.ringCatSheaf : D'.subscheme.Modules) ⟶
              (Scheme.Modules.pushforward D.subschemeι).obj
                (SheafOfModules.unit D.subscheme.ringCatSheaf : D.subscheme.Modules))
          (hfg : f ≫ g = 0),
          (ShortComplex.mk f g hfg).ShortExact)
