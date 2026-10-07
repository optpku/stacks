module

public import ReasLib.Algebra.Biderivation
import StacksCheckRecall

@[expose] public section

universe u v w

/- Definition 92.13.1: Let A → B be a ring map. Let M be a (B, B)-bimodule over A.
An A-biderivation is an A-linear map λ : B → M such that λ (x * y) = x λ(y) + λ(x) y. -/
@[stacks 09CE]
#check (Biderivation : ∀ (A : Type u) (B : Type v) (M : Type w),
  [CommRing A] → [CommRing B] → [Algebra A B] →
  [AddCommGroup M] → [Module A M] → [Module B M] → [Module Bᵐᵒᵖ M] →
  [IsScalarTower A B M] → [IsScalarTower A Bᵐᵒᵖ M] →
  [SMulCommClass B Bᵐᵒᵖ M] → Type (max v w))

#check Biderivation.ofLinearMap
#check Biderivation.apply
#check Biderivation.leibniz
#check Biderivation.spec
