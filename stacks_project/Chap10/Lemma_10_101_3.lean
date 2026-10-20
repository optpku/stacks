module

public import ReasLib.Algebra.Module.Basis.Nilpotent
import StacksCheckRecall

/-!
# Lifting a basis across a nilpotent ideal

@stack 051H
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped Pointwise

universe u v

section

variable {R : Type u} [CommRing R]
variable {A : Type v}
variable {M : Type u} [AddCommGroup M] [Module R M]

/- Lemma 10.101.3 (051H): if `I` is nilpotent, the images of a family `x : A → M` form an
`R ⧸ I`-basis of `M / (I • ⊤)`, and `Tor₁[R](R ⧸ I, M)` vanishes, then `x` is an `R`-basis of `M`.
The source-facing bridge is `Module.Basis.Nilpotent.of_quotient_basis_of_tor_one`; the canonical
universe-polymorphic owner uses injectivity of `I.tensorMul M`. -/
@[stacks 051H]
#check (Module.Basis.Nilpotent.of_quotient_basis_of_tor_one :
  ∀ (I : Ideal R) (x : A → M), IsNilpotent I →
    ∀ (bbar : Module.Basis A (R ⧸ I)
      (M ⧸ (I • (⊤ : Submodule R M)))),
      (∀ a, bbar a = Submodule.mkQ (I • (⊤ : Submodule R M)) (x a)) →
    IsZero (Tor₁[R](R ⧸ I, M)) →
    ∃ b : Module.Basis A R M, ∀ a, b a = x a)

end
