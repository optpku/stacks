/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Module.FiniteLength.Determinant.Exact
public import ReasLib.Algebra.Module.FiniteLength.Determinant.Functoriality
public import ReasLib.Algebra.Category.ModuleCat.ChangeOfRings.Exact
public import Mathlib.RingTheory.LocalRing.Length
public import Mathlib.LinearAlgebra.Finsupp.LSum
public import Mathlib.LinearAlgebra.TensorProduct.Map

/-!
# Determinant lines under restriction of scalars

A local homomorphism inducing an equivalence on residue fields transports admissible
determinant symbols, and hence determinant lines, across restriction of scalars.
-/

@[expose] public section

noncomputable section

open CategoryTheory
open scoped TensorProduct

universe u u' v

namespace Module.FiniteLengthDeterminant.Restriction

variable {R' : Type u'} {R : Type u} [CommRing R'] [CommRing R]
variable [IsLocalRing R'] [IsLocalRing R]
variable (f : R' →+* R) [IsLocalHom f]

/-- The residue-field equivalence induced by a bijective residue-field map. -/
noncomputable def residueEquiv
    (hκ : Function.Bijective (IsLocalRing.ResidueField.map f)) :
    IsLocalRing.ResidueField R' ≃+* IsLocalRing.ResidueField R :=
  RingEquiv.ofBijective (IsLocalRing.ResidueField.map f) hκ

/-- The forward ring homomorphism of `residueEquiv` is the induced residue-field map. -/
theorem residueEquiv_toRingHom
    (hκ : Function.Bijective (IsLocalRing.ResidueField.map f)) :
    (residueEquiv f hκ).toRingHom = IsLocalRing.ResidueField.map f := sorry

/-- The induced residue-field equivalence and its inverse form an inverse pair of ring maps. -/
instance residueEquiv_toSymmInvPair
    (hκ : Function.Bijective (IsLocalRing.ResidueField.map f)) :
    RingHomInvPair (residueEquiv f hκ).toRingHom (residueEquiv f hκ).symm.toRingHom :=
  RingHomInvPair.of_ringEquiv (residueEquiv f hκ)

/-- The inverse and forward maps of the induced residue-field equivalence form an inverse pair. -/
instance residueEquiv_symmToInvPair
    (hκ : Function.Bijective (IsLocalRing.ResidueField.map f)) :
    RingHomInvPair (residueEquiv f hκ).symm.toRingHom (residueEquiv f hκ).toRingHom :=
  RingHomInvPair.of_ringEquiv_symm (residueEquiv f hκ)

/-- Finite length is preserved by restriction along a local homomorphism inducing a residue-field
equivalence. -/
theorem isFiniteLength (hκ : Function.Bijective (IsLocalRing.ResidueField.map f))
    (M : ModuleCat.{v} R) (hM : IsFiniteLength R M) :
    IsFiniteLength R' ((ModuleCat.restrictScalars f).obj M) := sorry

/-- Restriction along `f` does not change the natural-number length indexing determinant
symbols. -/
theorem length_eq (hκ : Function.Bijective (IsLocalRing.ResidueField.map f))
    (M : ModuleCat.{v} R) (hM : IsFiniteLength R M) :
    length R' ((ModuleCat.restrictScalars f).obj M) (isFiniteLength f hκ M hM) =
      length R M hM := sorry

/-- Reindex an admissible determinant sequence after restriction of scalars. -/
def sequence (hκ : Function.Bijective (IsLocalRing.ResidueField.map f))
    (M : ModuleCat.{v} R) (hM : IsFiniteLength R M) (s : Symbol R M hM) :
    Fin (length R' ((ModuleCat.restrictScalars f).obj M)
      (isFiniteLength f hκ M hM)) → (ModuleCat.restrictScalars f).obj M :=
  fun i ↦ s.1 (finCongr (length_eq f hκ M hM) i)

/-- Evaluation of the restricted determinant sequence is the corresponding evaluation of the
original sequence. -/
theorem sequence_apply (hκ : Function.Bijective (IsLocalRing.ResidueField.map f))
    (M : ModuleCat.{v} R) (hM : IsFiniteLength R M) (s : Symbol R M hM)
    (i : Fin (length R' ((ModuleCat.restrictScalars f).obj M)
      (isFiniteLength f hκ M hM))) :
    sequence f hκ M hM s i = s.1 (finCongr (length_eq f hκ M hM) i) := sorry

/-- A determinant sequence admissible over `R` remains admissible after restriction to `R'`. -/
theorem sequence_isAdmissible
    (hκ : Function.Bijective (IsLocalRing.ResidueField.map f))
    (M : ModuleCat.{v} R) (hM : IsFiniteLength R M) (s : Symbol R M hM) :
    IsAdmissible R' ((ModuleCat.restrictScalars f).obj M)
      (isFiniteLength f hκ M hM) (sequence f hκ M hM s) := sorry

/-- The admissible determinant symbol obtained by restriction of scalars. -/
def symbol (hκ : Function.Bijective (IsLocalRing.ResidueField.map f))
    (M : ModuleCat.{v} R) (hM : IsFiniteLength R M) (s : Symbol R M hM) :
    Symbol R' ((ModuleCat.restrictScalars f).obj M) (isFiniteLength f hκ M hM) :=
  ⟨sequence f hκ M hM s, sequence_isAdmissible f hκ M hM s⟩

/-- The underlying sequence of a restricted determinant symbol is `sequence`. -/
theorem symbol_coe (hκ : Function.Bijective (IsLocalRing.ResidueField.map f))
    (M : ModuleCat.{v} R) (hM : IsFiniteLength R M) (s : Symbol R M hM) :
    (symbol f hκ M hM s).1 = sequence f hκ M hM s := sorry

/-- The semilinear map from the free module on `R`-symbols to the restricted determinant line. -/
def freeHom (hκ : Function.Bijective (IsLocalRing.ResidueField.map f))
    (M : ModuleCat.{v} R) (hM : IsFiniteLength R M) :
    Free R M hM →ₛₗ[(residueEquiv f hκ).symm.toRingHom]
      Module.FiniteLengthDeterminant R' ((ModuleCat.restrictScalars f).obj M)
        (isFiniteLength f hκ M hM) :=
  Finsupp.lsum (IsLocalRing.ResidueField R') fun s ↦
    (LinearMap.toSpanSingleton (IsLocalRing.ResidueField R')
      (Module.FiniteLengthDeterminant R' ((ModuleCat.restrictScalars f).obj M)
        (isFiniteLength f hκ M hM))
      (Module.FiniteLengthDeterminant.symbol R' ((ModuleCat.restrictScalars f).obj M)
        (isFiniteLength f hκ M hM) (symbol f hκ M hM s))).comp
      (residueEquiv f hκ).symm.toRingHom.toSemilinearMap

/-- The free semilinear map sends a basis symbol to its restricted determinant symbol. -/
theorem freeHom_single
    (hκ : Function.Bijective (IsLocalRing.ResidueField.map f))
    (M : ModuleCat.{v} R) (hM : IsFiniteLength R M) (s : Symbol R M hM) :
    freeHom f hκ M hM (Finsupp.single s 1) =
      Module.FiniteLengthDeterminant.symbol R' ((ModuleCat.restrictScalars f).obj M)
        (isFiniteLength f hκ M hM) (symbol f hκ M hM s) := sorry

/-- The free semilinear symbol map sends the determinant-relation submodule into zero. -/
theorem relationSubmodule_le_ker
    (hκ : Function.Bijective (IsLocalRing.ResidueField.map f))
    (M : ModuleCat.{v} R) (hM : IsFiniteLength R M) :
    Module.FiniteLengthDeterminant.relationSubmodule R M hM ≤
      LinearMap.ker (freeHom f hκ M hM) := sorry

/-- The semilinear determinant map induced by restriction of scalars. -/
def hom (hκ : Function.Bijective (IsLocalRing.ResidueField.map f))
    (M : ModuleCat.{v} R) (hM : IsFiniteLength R M) :
    Module.FiniteLengthDeterminant R M hM →ₛₗ[(residueEquiv f hκ).symm.toRingHom]
      Module.FiniteLengthDeterminant R' ((ModuleCat.restrictScalars f).obj M)
        (isFiniteLength f hκ M hM) :=
  (Module.FiniteLengthDeterminant.relationSubmodule R M hM).liftQ
    (freeHom f hκ M hM) (relationSubmodule_le_ker f hκ M hM)

/-- The restriction map carries each determinant symbol to its restricted symbol. -/
theorem hom_symbol (hκ : Function.Bijective (IsLocalRing.ResidueField.map f))
    (M : ModuleCat.{v} R) (hM : IsFiniteLength R M) (s : Symbol R M hM) :
    hom f hκ M hM (Module.FiniteLengthDeterminant.symbol R M hM s) =
      Module.FiniteLengthDeterminant.symbol R' ((ModuleCat.restrictScalars f).obj M)
        (isFiniteLength f hκ M hM) (symbol f hκ M hM s) := sorry

/-- The inverse function of the restriction determinant map is a left inverse. -/
theorem hom_invFun_left
    (hκ : Function.Bijective (IsLocalRing.ResidueField.map f))
    (M : ModuleCat.{v} R) (hM : IsFiniteLength R M) :
    Function.LeftInverse (Function.invFun (hom f hκ M hM)) (hom f hκ M hM) := sorry

/-- The inverse function of the restriction determinant map is a right inverse. -/
theorem hom_invFun_right
    (hκ : Function.Bijective (IsLocalRing.ResidueField.map f))
    (M : ModuleCat.{v} R) (hM : IsFiniteLength R M) :
    Function.RightInverse (Function.invFun (hom f hκ M hM)) (hom f hκ M hM) := sorry

/-- The canonical semilinear equivalence of determinant lines under restriction of scalars. -/
noncomputable def equiv
    (hκ : Function.Bijective (IsLocalRing.ResidueField.map f))
    (M : ModuleCat.{v} R) (hM : IsFiniteLength R M) :
    Module.FiniteLengthDeterminant R M hM ≃ₛₗ[(residueEquiv f hκ).symm.toRingHom]
      Module.FiniteLengthDeterminant R' ((ModuleCat.restrictScalars f).obj M)
        (isFiniteLength f hκ M hM) :=
  { hom f hκ M hM with
    invFun := Function.invFun (hom f hκ M hM)
    left_inv := hom_invFun_left f hκ M hM
    right_inv := hom_invFun_right f hκ M hM }

/-- The restriction equivalence carries each determinant symbol to its restricted symbol. -/
theorem equiv_symbol (hκ : Function.Bijective (IsLocalRing.ResidueField.map f))
    (M : ModuleCat.{v} R) (hM : IsFiniteLength R M) (s : Symbol R M hM) :
    equiv f hκ M hM (Module.FiniteLengthDeterminant.symbol R M hM s) =
      Module.FiniteLengthDeterminant.symbol R' ((ModuleCat.restrictScalars f).obj M)
        (isFiniteLength f hκ M hM) (symbol f hκ M hM s) := sorry

/-- Restriction of determinant lines is natural in isomorphisms of finite-length modules. -/
theorem equiv_naturality
    (hκ : Function.Bijective (IsLocalRing.ResidueField.map f))
    {M N : ModuleCat.{v} R} (hM : IsFiniteLength R M) (hN : IsFiniteLength R N)
    (e : M ≅ N) (x : Module.FiniteLengthDeterminant R M hM) :
    equiv f hκ N hN
        (Module.FiniteLengthDeterminant.mapEquiv hM hN e.toLinearEquiv x) =
      (Module.FiniteLengthDeterminant.mapEquiv
        (isFiniteLength f hκ M hM) (isFiniteLength f hκ N hN)
        ((ModuleCat.restrictScalars f).mapIso e).toLinearEquiv) (equiv f hκ M hM x) := sorry

/-- Restriction of determinant lines commutes with the determinant equivalence attached to a
short exact sequence. -/
theorem equiv_exact
    (hκ : Function.Bijective (IsLocalRing.ResidueField.map f))
    (S : ShortComplex (ModuleCat.{v} R))
    (h₁ : IsFiniteLength R S.X₁) (h₂ : IsFiniteLength R S.X₂)
    (h₃ : IsFiniteLength R S.X₃) (hS : S.ShortExact)
    (x : Module.FiniteLengthDeterminant R S.X₁ h₁ ⊗[IsLocalRing.ResidueField R]
      Module.FiniteLengthDeterminant R S.X₃ h₃) :
    Module.FiniteLengthDeterminant.exactEquiv
      (S.map (ModuleCat.restrictScalars f))
      (isFiniteLength f hκ S.X₁ h₁) (isFiniteLength f hκ S.X₂ h₂)
      (isFiniteLength f hκ S.X₃ h₃)
      (hS.map_of_exact (ModuleCat.restrictScalars f))
      (TensorProduct.congr (equiv f hκ S.X₁ h₁) (equiv f hκ S.X₃ h₃) x) =
      equiv f hκ S.X₂ h₂
        (Module.FiniteLengthDeterminant.exactEquiv S h₁ h₂ h₃ hS x) := sorry

end Module.FiniteLengthDeterminant.Restriction
