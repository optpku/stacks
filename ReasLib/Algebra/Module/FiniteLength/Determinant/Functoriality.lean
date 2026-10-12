/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Module.FiniteLength.Determinant

/-!
# Functoriality of finite-length determinant lines

An equivalence of finite-length modules acts on admissible sequences and therefore on their
determinant lines. The quotient construction is kept behind its symbol-level specification.
-/

@[expose] public section

noncomputable section

universe u v

namespace Module.FiniteLengthDeterminant

variable {R : Type u} [CommRing R] [IsLocalRing R]
variable {M N P : Type v}
variable [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
variable [AddCommGroup P] [Module R P]

/-- Apply a linear equivalence to an admissible sequence, reindexing by preservation of length. -/
def mapSequence (hM : IsFiniteLength R M) (hN : IsFiniteLength R N)
    (e : M ≃ₗ[R] N) (s : Symbol R M hM) :
    Fin (length R N hN) → N :=
  fun i ↦ e (s.1 ((finCongr (congrArg ENat.toNat e.length_eq)).symm i))

/-- The image of an admissible sequence under a linear equivalence is admissible. -/
theorem mapSequence_isAdmissible (hM : IsFiniteLength R M) (hN : IsFiniteLength R N)
    (e : M ≃ₗ[R] N) (s : Symbol R M hM) :
    IsAdmissible R N hN (mapSequence hM hN e s) := sorry

/-- The admissible determinant symbol obtained by applying a linear equivalence entrywise. -/
def mapSymbol (hM : IsFiniteLength R M) (hN : IsFiniteLength R N)
    (e : M ≃ₗ[R] N) (s : Symbol R M hM) : Symbol R N hN :=
  ⟨mapSequence hM hN e s, mapSequence_isAdmissible hM hN e s⟩

/-- Mapping admissible symbols along a linear equivalence kills every determinant relation. -/
theorem mapRelation (hM : IsFiniteLength R M) (hN : IsFiniteLength R N)
    (e : M ≃ₗ[R] N) (x : Free R M hM) (hx : Relation R M hM x) :
    Finsupp.linearCombination (IsLocalRing.ResidueField R)
      (fun s ↦ symbol R N hN (mapSymbol hM hN e s)) x = 0 := sorry

/-- The residue-field-linear map on finite-length determinant lines induced by a module
equivalence. -/
def mapHom (hM : IsFiniteLength R M) (hN : IsFiniteLength R N)
    (e : M ≃ₗ[R] N) :
    Module.FiniteLengthDeterminant R M hM →ₗ[IsLocalRing.ResidueField R]
      Module.FiniteLengthDeterminant R N hN :=
  lift R M hM
    (Finsupp.linearCombination (IsLocalRing.ResidueField R)
      (fun s ↦ symbol R N hN (mapSymbol hM hN e s)))
    (mapRelation hM hN e)

/-- The induced determinant map applies the module equivalence entrywise to symbols. -/
theorem mapHom_symbol (hM : IsFiniteLength R M) (hN : IsFiniteLength R N)
    (e : M ≃ₗ[R] N) (s : Symbol R M hM) :
    mapHom hM hN e (symbol R M hM s) = symbol R N hN (mapSymbol hM hN e s) := sorry

/-- The determinant map induced by the inverse module equivalence is a left inverse. -/
theorem mapHom_leftInverse (hM : IsFiniteLength R M) (hN : IsFiniteLength R N)
    (e : M ≃ₗ[R] N) :
    Function.LeftInverse (mapHom hN hM e.symm) (mapHom hM hN e) := sorry

/-- The determinant map induced by the inverse module equivalence is a right inverse. -/
theorem mapHom_rightInverse (hM : IsFiniteLength R M) (hN : IsFiniteLength R N)
    (e : M ≃ₗ[R] N) :
    Function.RightInverse (mapHom hN hM e.symm) (mapHom hM hN e) := sorry

/-- The canonical equivalence of finite-length determinant lines induced by a module
equivalence. -/
def mapEquiv (hM : IsFiniteLength R M) (hN : IsFiniteLength R N)
    (e : M ≃ₗ[R] N) :
    Module.FiniteLengthDeterminant R M hM ≃ₗ[IsLocalRing.ResidueField R]
      Module.FiniteLengthDeterminant R N hN :=
  { mapHom hM hN e with
    invFun := mapHom hN hM e.symm
    left_inv := mapHom_leftInverse hM hN e
    right_inv := mapHom_rightInverse hM hN e }

/-- The induced determinant equivalence applies the module equivalence entrywise to symbols. -/
theorem mapEquiv_symbol (hM : IsFiniteLength R M) (hN : IsFiniteLength R N)
    (e : M ≃ₗ[R] N) (s : Symbol R M hM) :
    mapEquiv hM hN e (symbol R M hM s) = symbol R N hN (mapSymbol hM hN e s) := sorry

/-- The determinant equivalence induced by the identity is the identity. -/
theorem mapEquiv_refl (hM : IsFiniteLength R M) :
    mapEquiv hM hM (LinearEquiv.refl R M) =
      LinearEquiv.refl (IsLocalRing.ResidueField R)
        (Module.FiniteLengthDeterminant R M hM) := sorry

/-- Determinant equivalences respect composition of module equivalences. -/
theorem mapEquiv_trans (hM : IsFiniteLength R M) (hN : IsFiniteLength R N)
    (hP : IsFiniteLength R P) (e : M ≃ₗ[R] N) (f : N ≃ₗ[R] P) :
    (mapEquiv hM hN e).trans (mapEquiv hN hP f) = mapEquiv hM hP (e.trans f) := sorry

end Module.FiniteLengthDeterminant
