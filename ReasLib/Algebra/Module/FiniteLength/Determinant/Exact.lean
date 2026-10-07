module

public import ReasLib.Algebra.Module.FiniteLength.Determinant.Dimension
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.LinearAlgebra.TensorProduct.Basic

/-!
# Additivity of the finite-length determinant line

This file constructs the determinant-line comparison attached to a short exact sequence of
finite-length modules. Its forward map concatenates a symbol in the left term with chosen lifts
of a symbol in the right term.
-/

@[expose] public section

noncomputable section

open CategoryTheory
open scoped TensorProduct

universe u v

namespace Module.FiniteLengthDeterminant

variable {R : Type u} [CommRing R] [IsLocalRing R]

/-- The sequence in the middle term obtained by concatenating the image of a left-hand
determinant symbol with chosen lifts of a right-hand determinant symbol. -/
def exactSequence (S : ShortComplex (ModuleCat.{v} R))
    (h₁ : IsFiniteLength R S.X₁) (h₂ : IsFiniteLength R S.X₂)
    (h₃ : IsFiniteLength R S.X₃) (e₁ : Symbol R S.X₁ h₁)
    (e₃ : Symbol R S.X₃ h₃) : Fin (length R S.X₂ h₂) → S.X₂ :=
  fun i ↦
    if hi : i.val < length R S.X₁ h₁ then
      S.f.hom (e₁.1 ⟨i.val, hi⟩)
    else if hzero : length R S.X₃ h₃ = 0 then
      0
    else
      Function.invFun S.g.hom
        (e₃.1 (@Fin.ofNat (length R S.X₃ h₃) ⟨hzero⟩
          (i.val - length R S.X₁ h₁)))

/-- Concatenation along a short exact sequence produces an admissible sequence in its middle
term. -/
theorem exactSequence_isAdmissible (S : ShortComplex (ModuleCat.{v} R))
    (h₁ : IsFiniteLength R S.X₁) (h₂ : IsFiniteLength R S.X₂)
    (h₃ : IsFiniteLength R S.X₃) (hS : S.ShortExact)
    (e₁ : Symbol R S.X₁ h₁)
    (he₁ : symbol R S.X₁ h₁ e₁ ≠ 0) (e₃ : Symbol R S.X₃ h₃) :
    IsAdmissible R S.X₂ h₂ (exactSequence S h₁ h₂ h₃ e₁ e₃) := sorry

/-- The determinant symbol in the middle term obtained by the short-exact concatenation
formula. -/
def exactSymbol (S : ShortComplex (ModuleCat.{v} R))
    (h₁ : IsFiniteLength R S.X₁) (h₂ : IsFiniteLength R S.X₂)
    (h₃ : IsFiniteLength R S.X₃) (hS : S.ShortExact)
    (e₁ : Symbol R S.X₁ h₁) (e₃ : Symbol R S.X₃ h₃) :
    Module.FiniteLengthDeterminant R S.X₂ h₂ :=
  @dite (Module.FiniteLengthDeterminant R S.X₂ h₂)
    (symbol R S.X₁ h₁ e₁ = 0)
    (Classical.decEq (Module.FiniteLengthDeterminant R S.X₁ h₁)
      (symbol R S.X₁ h₁ e₁) 0)
    (fun _ ↦ 0)
    (fun he₁ ↦ symbol R S.X₂ h₂
      ⟨exactSequence S h₁ h₂ h₃ e₁ e₃,
        exactSequence_isAdmissible S h₁ h₂ h₃ hS e₁ he₁ e₃⟩)

/-- For a nonzero left symbol, `exactSymbol` is represented by the concatenated middle-term
sequence. -/
theorem exactSymbol_of_ne_zero (S : ShortComplex (ModuleCat.{v} R))
    (h₁ : IsFiniteLength R S.X₁) (h₂ : IsFiniteLength R S.X₂)
    (h₃ : IsFiniteLength R S.X₃) (hS : S.ShortExact)
    (e₁ : Symbol R S.X₁ h₁) (he₁ : symbol R S.X₁ h₁ e₁ ≠ 0)
    (e₃ : Symbol R S.X₃ h₃) :
    exactSymbol S h₁ h₂ h₃ hS e₁ e₃ =
      symbol R S.X₂ h₂
        ⟨exactSequence S h₁ h₂ h₃ e₁ e₃,
          exactSequence_isAdmissible S h₁ h₂ h₃ hS e₁ he₁ e₃⟩ := sorry

/-- For a fixed left symbol, the short-exact concatenation kills every defining relation in
the right determinant line. -/
theorem exactRight_relation (S : ShortComplex (ModuleCat.{v} R))
    (h₁ : IsFiniteLength R S.X₁) (h₂ : IsFiniteLength R S.X₂)
    (h₃ : IsFiniteLength R S.X₃) (hS : S.ShortExact)
    (e₁ : Symbol R S.X₁ h₁) (x : Free R S.X₃ h₃)
    (hx : Relation R S.X₃ h₃ x) :
    Finsupp.linearCombination (IsLocalRing.ResidueField R)
      (fun e₃ ↦ exactSymbol S h₁ h₂ h₃ hS e₁ e₃) x = 0 := sorry

/-- The right-linear map obtained from the short-exact concatenation formula after fixing the
left symbol. -/
def exactRightMap (S : ShortComplex (ModuleCat.{v} R))
    (h₁ : IsFiniteLength R S.X₁) (h₂ : IsFiniteLength R S.X₂)
    (h₃ : IsFiniteLength R S.X₃) (hS : S.ShortExact)
    (e₁ : Symbol R S.X₁ h₁) :
    Module.FiniteLengthDeterminant R S.X₃ h₃ →ₗ[IsLocalRing.ResidueField R]
      Module.FiniteLengthDeterminant R S.X₂ h₂ :=
  lift R S.X₃ h₃
    (Finsupp.linearCombination (IsLocalRing.ResidueField R)
      (fun e₃ ↦ exactSymbol S h₁ h₂ h₃ hS e₁ e₃))
    (exactRight_relation S h₁ h₂ h₃ hS e₁)

/-- The right-linear short-exact map sends a right determinant symbol to the corresponding
concatenated middle-term symbol. -/
theorem exactRightMap_symbol (S : ShortComplex (ModuleCat.{v} R))
    (h₁ : IsFiniteLength R S.X₁) (h₂ : IsFiniteLength R S.X₂)
    (h₃ : IsFiniteLength R S.X₃) (hS : S.ShortExact)
    (e₁ : Symbol R S.X₁ h₁) (e₃ : Symbol R S.X₃ h₃) :
    exactRightMap S h₁ h₂ h₃ hS e₁ (symbol R S.X₃ h₃ e₃) =
      exactSymbol S h₁ h₂ h₃ hS e₁ e₃ := sorry

/-- The left linear extension of the family of right-linear short-exact concatenation maps
kills every defining relation in the left determinant line. -/
theorem exactLeft_relation (S : ShortComplex (ModuleCat.{v} R))
    (h₁ : IsFiniteLength R S.X₁) (h₂ : IsFiniteLength R S.X₂)
    (h₃ : IsFiniteLength R S.X₃) (hS : S.ShortExact)
    (x : Free R S.X₁ h₁) (hx : Relation R S.X₁ h₁ x) :
    Finsupp.linearCombination (IsLocalRing.ResidueField R)
      (fun e₁ ↦ exactRightMap S h₁ h₂ h₃ hS e₁) x = 0 := sorry

/-- The bilinear determinant-line map supplied by a short exact sequence. -/
def exactBilinear (S : ShortComplex (ModuleCat.{v} R))
    (h₁ : IsFiniteLength R S.X₁) (h₂ : IsFiniteLength R S.X₂)
    (h₃ : IsFiniteLength R S.X₃) (hS : S.ShortExact) :
    Module.FiniteLengthDeterminant R S.X₁ h₁ →ₗ[IsLocalRing.ResidueField R]
      Module.FiniteLengthDeterminant R S.X₃ h₃ →ₗ[IsLocalRing.ResidueField R]
        Module.FiniteLengthDeterminant R S.X₂ h₂ :=
  lift R S.X₁ h₁
    (Finsupp.linearCombination (IsLocalRing.ResidueField R)
      (fun e₁ ↦ exactRightMap S h₁ h₂ h₃ hS e₁))
    (exactLeft_relation S h₁ h₂ h₃ hS)

/-- Evaluating the short-exact bilinear map on a left determinant symbol gives its associated
right-linear concatenation map. -/
theorem exactBilinear_symbol (S : ShortComplex (ModuleCat.{v} R))
    (h₁ : IsFiniteLength R S.X₁) (h₂ : IsFiniteLength R S.X₂)
    (h₃ : IsFiniteLength R S.X₃) (hS : S.ShortExact)
    (e₁ : Symbol R S.X₁ h₁) :
    exactBilinear S h₁ h₂ h₃ hS (symbol R S.X₁ h₁ e₁) =
      exactRightMap S h₁ h₂ h₃ hS e₁ := sorry

/-- The forward determinant-line map associated to a short exact sequence. -/
def exactHom (S : ShortComplex (ModuleCat.{v} R))
    (h₁ : IsFiniteLength R S.X₁) (h₂ : IsFiniteLength R S.X₂)
    (h₃ : IsFiniteLength R S.X₃) (hS : S.ShortExact) :
    Module.FiniteLengthDeterminant R S.X₁ h₁ ⊗[IsLocalRing.ResidueField R]
        Module.FiniteLengthDeterminant R S.X₃ h₃ →ₗ[IsLocalRing.ResidueField R]
      Module.FiniteLengthDeterminant R S.X₂ h₂ :=
  TensorProduct.lift (exactBilinear S h₁ h₂ h₃ hS)

/-- On a pure tensor of determinant symbols, `exactHom` evaluates to the corresponding
short-exact concatenation symbol. -/
theorem exactHom_tmul_symbol (S : ShortComplex (ModuleCat.{v} R))
    (h₁ : IsFiniteLength R S.X₁) (h₂ : IsFiniteLength R S.X₂)
    (h₃ : IsFiniteLength R S.X₃) (hS : S.ShortExact)
    (e₁ : Symbol R S.X₁ h₁) (e₃ : Symbol R S.X₃ h₃) :
    exactHom S h₁ h₂ h₃ hS
        (symbol R S.X₁ h₁ e₁ ⊗ₜ[IsLocalRing.ResidueField R]
          symbol R S.X₃ h₃ e₃) =
      exactSymbol S h₁ h₂ h₃ hS e₁ e₃ := sorry

/-- The inverse function selected from the concrete short-exact determinant map is a left
inverse. -/
theorem exactHom_invFun_left (S : ShortComplex (ModuleCat.{v} R))
    (h₁ : IsFiniteLength R S.X₁) (h₂ : IsFiniteLength R S.X₂)
    (h₃ : IsFiniteLength R S.X₃) (hS : S.ShortExact) :
    Function.LeftInverse (Function.invFun (exactHom S h₁ h₂ h₃ hS))
      (exactHom S h₁ h₂ h₃ hS) := sorry

/-- The inverse function selected from the concrete short-exact determinant map is a right
inverse. -/
theorem exactHom_invFun_right (S : ShortComplex (ModuleCat.{v} R))
    (h₁ : IsFiniteLength R S.X₁) (h₂ : IsFiniteLength R S.X₂)
    (h₃ : IsFiniteLength R S.X₃) (hS : S.ShortExact) :
    Function.RightInverse (Function.invFun (exactHom S h₁ h₂ h₃ hS))
      (exactHom S h₁ h₂ h₃ hS) := sorry

/-- The canonical determinant-line equivalence associated to a short exact sequence of
finite-length modules. -/
def exactEquiv (S : ShortComplex (ModuleCat.{v} R))
    (h₁ : IsFiniteLength R S.X₁) (h₂ : IsFiniteLength R S.X₂)
    (h₃ : IsFiniteLength R S.X₃) (hS : S.ShortExact) :
    Module.FiniteLengthDeterminant R S.X₁ h₁ ⊗[IsLocalRing.ResidueField R]
        Module.FiniteLengthDeterminant R S.X₃ h₃ ≃ₗ[IsLocalRing.ResidueField R]
      Module.FiniteLengthDeterminant R S.X₂ h₂ :=
  { exactHom S h₁ h₂ h₃ hS with
    invFun := Function.invFun (exactHom S h₁ h₂ h₃ hS)
    left_inv := exactHom_invFun_left S h₁ h₂ h₃ hS
    right_inv := exactHom_invFun_right S h₁ h₂ h₃ hS }

/-- On determinant symbols, `exactEquiv` is concatenation of the injected left sequence and
chosen lifts of the right sequence. -/
theorem exactEquiv_tmul_symbol (S : ShortComplex (ModuleCat.{v} R))
    (h₁ : IsFiniteLength R S.X₁) (h₂ : IsFiniteLength R S.X₂)
    (h₃ : IsFiniteLength R S.X₃) (hS : S.ShortExact)
    (e₁ : Symbol R S.X₁ h₁) (he₁ : symbol R S.X₁ h₁ e₁ ≠ 0)
    (e₃ : Symbol R S.X₃ h₃) :
    exactEquiv S h₁ h₂ h₃ hS
        (symbol R S.X₁ h₁ e₁ ⊗ₜ[IsLocalRing.ResidueField R]
          symbol R S.X₃ h₃ e₃) =
      symbol R S.X₂ h₂
        ⟨exactSequence S h₁ h₂ h₃ e₁ e₃,
          exactSequence_isAdmissible S h₁ h₂ h₃ hS e₁ he₁ e₃⟩ := sorry

end Module.FiniteLengthDeterminant
