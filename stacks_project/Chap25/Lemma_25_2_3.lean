/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Sites.Family.FormalCoproduct.Augmentation.Over
import StacksCheckRecall

universe w v u

namespace CategoryTheory

open CategoryTheory.Limits
open scoped CategoryTheory.SemiRepresentableFamily

variable {C : Type u} [Category.{v} C] (J : Type w) (X : C)

/- Lemma 25.2.3 (1), tag `01G2`: `SR(C)` has coproducts. -/
@[stacks 01G2 "(1), coproducts"]
#check (inferInstance : HasCoproducts.{w} SR(C))

/- Lemma 25.2.3 (2), tag `01G2`: the formal-coproduct presheaf functor preserves
`J`-indexed coproducts. -/
@[stacks 01G2 "(1), coproduct preservation"]
#check (inferInstance :
  PreservesColimitsOfShape (Discrete J)
    (Limits.FormalCoproduct.toPresheaf :
      SR(C) ⥤ (Cᵒᵖ ⥤ Type (max w v))))

/- Lemma 25.2.3 (3), tag `01G2`: the formal-coproduct presheaf functor preserves limits. -/
@[stacks 01G2 "(2), limit preservation"]
#check (inferInstance :
  PreservesLimits
    (Limits.FormalCoproduct.toPresheaf :
      SR(C) ⥤ (Cᵒᵖ ⥤ Type (max w v))))

/- Lemma 25.2.3 (4), tag `01G2`: pullbacks of semi-representable families are inherited
componentwise. -/
section

variable [HasPullbacks C]

@[stacks 01G2 "(3), pullbacks"]
#check (inferInstance : HasPullbacks SR(C))

end

/- Lemma 25.2.3 (5), tag `01G2`: binary products of semi-representable families are inherited
componentwise. -/
section

variable [HasBinaryProducts C]

@[stacks 01G2 "(4), binary products"]
#check (inferInstance : HasBinaryProducts SR(C))

end

/- Lemma 25.2.3 (6), tag `01G2`: equalizers of semi-representable families are inherited
componentwise. -/
section

variable [HasEqualizers C]

@[stacks 01G2 "(5), equalizers"]
#check (inferInstance : HasEqualizers SR(C))

end

/- Lemma 25.2.3 (7), tag `01G2`: a terminal object of `C` yields one of `SR(C)`. -/
section

variable [HasTerminal C]

@[stacks 01G2 "(6), terminal object"]
#check (inferInstance : HasTerminal SR(C))

end

/- Lemma 25.2.3 (8), tag `01G2`: `SR(C, X)` has coproducts. -/
@[stacks 01G2 "fixed target, coproducts"]
#check (inferInstance :
  HasCoproducts.{w} SR(C, X))

/- Lemma 25.2.3 (9), tag `01G2`: the augmentation functor from `SR(C, X)` to
`PSh(C) / h_X` preserves `J`-indexed coproducts. -/
@[stacks 01G2 "fixed target, coproduct preservation"]
#check (inferInstance :
  PreservesColimitsOfShape (Discrete J)
    (SemiRepresentableFamily.OverFamily.Augmentation.toOver X))

/- Lemma 25.2.3 (10), tag `01G2`: if `C` has pullbacks, then `SR(C, X)` has finite limits. -/
section

variable [HasPullbacks C]

@[stacks 01G2 "fixed target, finite limits"]
#check (inferInstance : HasFiniteLimits SR(C, X))

/- Lemma 25.2.3 (11), tag `01G2`: under the same pullback hypothesis, the augmented
presheaf functor of `SR(C, X)` preserves finite limits. -/
@[stacks 01G2 "fixed target, finite-limit preservation"]
#check (inferInstance :
  PreservesFiniteLimits (SemiRepresentableFamily.OverFamily.Augmentation.toOver X))

end

end CategoryTheory
