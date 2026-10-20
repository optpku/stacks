/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.EllipticCurve.WeierstrassQuotient

open CategoryTheory
open scoped Bicategory

universe u

/- Remark 105.6.2
The moduli stack of elliptic curves is the global quotient [W/H]. The observation
that algebraicity arguments produce global quotients about 50% of the time is informal.
-/
@[stacks 072U] #check
  (AlgebraicGeometry.EllipticCurve.equiv_weierstrassQuotient :
    ∃ e : AlgebraicGeometry.AlgebraicStack.WeierstrassQuotient.stack ⟶
        AlgebraicGeometry.EllipticCurve.moduli.{u},
      (FiberedCategoryOver.Groupoids.toBasedFunctor e).IsEquivalence ∧
        Nonempty
          (AlgebraicGeometry.AlgebraicStack.WeierstrassQuotient.atlas ≫ e ≅
            (AlgebraicGeometry.AlgebraicSpace.ofOverSliceEquiv
              AlgebraicGeometry.WeierstrassScheme.overInt).hom ≫
                AlgebraicGeometry.WeierstrassScheme.classifying.{u}))
