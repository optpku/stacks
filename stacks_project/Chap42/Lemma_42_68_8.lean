/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
import ReasLib.Algebra.Module.FiniteLength.Determinant.Restriction

open CategoryTheory
open scoped TensorProduct

universe u u' v

variable {R' : Type u'} {R : Type u} [CommRing R'] [CommRing R]
variable [IsLocalRing R'] [IsLocalRing R]

/- Lemma 42.68.8 (1): restriction of scalars preserves finite length when the local
homomorphism induces an equivalence of residue fields. -/
@[stacks 02PC] #check
  (Module.FiniteLengthDeterminant.Restriction.isFiniteLength :
    ∀ (f : R' →+* R) [IsLocalHom f]
      (hκ : Function.Bijective (IsLocalRing.ResidueField.map f))
      (M : ModuleCat.{v} R) (hM : IsFiniteLength R M),
      IsFiniteLength R' ((ModuleCat.restrictScalars f).obj M))

/- Lemma 42.68.8 (2): restriction of scalars canonically identifies the determinant lines,
semilinearly over the induced residue-field equivalence. -/
@[stacks 02PC] #check
  (Module.FiniteLengthDeterminant.Restriction.equiv :
    ∀ (f : R' →+* R) [IsLocalHom f]
      (hκ : Function.Bijective (IsLocalRing.ResidueField.map f))
      (M : ModuleCat.{v} R) (hM : IsFiniteLength R M),
      Module.FiniteLengthDeterminant R M hM ≃ₛₗ[
        (Module.FiniteLengthDeterminant.Restriction.residueEquiv f hκ).symm.toRingHom]
        Module.FiniteLengthDeterminant R' ((ModuleCat.restrictScalars f).obj M)
          (Module.FiniteLengthDeterminant.Restriction.isFiniteLength f hκ M hM))

#check
  (Module.FiniteLengthDeterminant.Restriction.equiv_symbol :
    ∀ (f : R' →+* R) [IsLocalHom f]
      (hκ : Function.Bijective (IsLocalRing.ResidueField.map f))
      (M : ModuleCat.{v} R) (hM : IsFiniteLength R M)
      (s : Module.FiniteLengthDeterminant.Symbol R M hM),
      Module.FiniteLengthDeterminant.Restriction.equiv f hκ M hM
          (Module.FiniteLengthDeterminant.symbol R M hM s) =
        Module.FiniteLengthDeterminant.symbol R' ((ModuleCat.restrictScalars f).obj M)
          (Module.FiniteLengthDeterminant.Restriction.isFiniteLength f hκ M hM)
          (Module.FiniteLengthDeterminant.Restriction.symbol f hκ M hM s))

/- Lemma 42.68.8 (3): the canonical determinant-line equivalence is natural in module
isomorphisms. -/
@[stacks 02PC] #check
  (Module.FiniteLengthDeterminant.Restriction.equiv_naturality :
    ∀ (f : R' →+* R) [IsLocalHom f]
      (hκ : Function.Bijective (IsLocalRing.ResidueField.map f))
      {M N : ModuleCat.{v} R} (hM : IsFiniteLength R M) (hN : IsFiniteLength R N)
      (e : M ≅ N) (x : Module.FiniteLengthDeterminant R M hM),
      Module.FiniteLengthDeterminant.Restriction.equiv f hκ N hN
          (Module.FiniteLengthDeterminant.mapEquiv hM hN e.toLinearEquiv x) =
        (Module.FiniteLengthDeterminant.mapEquiv
          (Module.FiniteLengthDeterminant.Restriction.isFiniteLength f hκ M hM)
          (Module.FiniteLengthDeterminant.Restriction.isFiniteLength f hκ N hN)
          ((ModuleCat.restrictScalars f).mapIso e).toLinearEquiv)
          (Module.FiniteLengthDeterminant.Restriction.equiv f hκ M hM x))

/- Lemma 42.68.8 (4): the canonical determinant-line equivalence is compatible with the
short-exact determinant equivalences. -/
@[stacks 02PC] #check
  (Module.FiniteLengthDeterminant.Restriction.equiv_exact :
    ∀ (f : R' →+* R) [IsLocalHom f]
      (hκ : Function.Bijective (IsLocalRing.ResidueField.map f))
      (S : ShortComplex (ModuleCat.{v} R))
      (h₁ : IsFiniteLength R S.X₁) (h₂ : IsFiniteLength R S.X₂)
      (h₃ : IsFiniteLength R S.X₃) (hS : S.ShortExact)
      (x : Module.FiniteLengthDeterminant R S.X₁ h₁ ⊗[IsLocalRing.ResidueField R]
        Module.FiniteLengthDeterminant R S.X₃ h₃),
      Module.FiniteLengthDeterminant.exactEquiv
          (S.map (ModuleCat.restrictScalars f))
          (Module.FiniteLengthDeterminant.Restriction.isFiniteLength f hκ S.X₁ h₁)
          (Module.FiniteLengthDeterminant.Restriction.isFiniteLength f hκ S.X₂ h₂)
          (Module.FiniteLengthDeterminant.Restriction.isFiniteLength f hκ S.X₃ h₃)
          (hS.map_of_exact (ModuleCat.restrictScalars f))
          (TensorProduct.congr
            (Module.FiniteLengthDeterminant.Restriction.equiv f hκ S.X₁ h₁)
            (Module.FiniteLengthDeterminant.Restriction.equiv f hκ S.X₃ h₃) x) =
        Module.FiniteLengthDeterminant.Restriction.equiv f hκ S.X₂ h₂
          (Module.FiniteLengthDeterminant.exactEquiv S h₁ h₂ h₃ hS x))
