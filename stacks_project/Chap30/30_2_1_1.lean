module

import ReasLib.Algebra.Module.LocalizedModule.Away.Cech.Product
import StacksCheckRecall

universe u v

variable {R : Type u} [CommRing R] {r : ℕ}
variable (f : Fin r → R) (M : Type (max u v)) [AddCommGroup M] [Module R M]

/- 30.2.1.1: the extended product-indexed localization complex
`0 → M → ∏ i₀, M_(f i₀) → ∏ i₀ i₁, M_(f i₀ f i₁) →
  ∏ i₀ i₁ i₂, M_(f i₀ f i₁ f i₂) → ...`. -/
@[stacks 01XA] #check
  (LocalizedModule.Away.Cech.Product.extended f M :
    CochainComplex (ModuleCat.{max u v} R) ℕ)
