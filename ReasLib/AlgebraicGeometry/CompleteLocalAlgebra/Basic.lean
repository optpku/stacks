/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.FiberedCategory.HomLift
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import ReasLib.RingTheory.Completion.LocalRing

/-!
# Complete local algebras over schemes

A complete local `S`-algebra is a Noetherian complete local ring `R` equipped with
`Spec R ⟶ S` whose residue field is of finite type over `S`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry IsLocalRing

noncomputable section

universe u

namespace AlgebraicGeometry

/-- A Noetherian complete local ring with a structure morphism to a scheme and
finite-type residue field over that scheme. -/
def CompleteLocalSAlgebra (S : Scheme.{u}) : Type (u + 1) :=
  Σ' ring : CommRingCat.{u},
    Σ' isLocalRing : IsLocalRing ring,
      Σ' isNoetherianRing : IsNoetherianRing ring,
        Σ' isCompleteLocalRing : IsCompleteLocalRing ring,
          Σ' toS : Spec ring ⟶ S,
            LocallyOfFiniteType (Spec.map (CommRingCat.ofHom
              (Ideal.Quotient.mk (@maximalIdeal ring inferInstance isLocalRing))) ≫ toS)

namespace CompleteLocalSAlgebra

variable {S : Scheme.{u}}

/-- The underlying ring carrier. -/
def carrier (R : CompleteLocalSAlgebra S) : Type u := R.1

/-- The commutative ring structure of the carrier. -/
instance commRing (R : CompleteLocalSAlgebra S) : CommRing R.carrier := R.1.commRing

/-- The carrier is a local ring. -/
instance isLocalRing (R : CompleteLocalSAlgebra S) : IsLocalRing R.carrier := R.2.1

/-- The carrier is Noetherian. -/
instance isNoetherianRing (R : CompleteLocalSAlgebra S) : IsNoetherianRing R.carrier := R.2.2.1

/-- The carrier is complete for its maximal-adic topology. -/
instance isCompleteLocalRing (R : CompleteLocalSAlgebra S) : IsCompleteLocalRing R.carrier :=
  R.2.2.2.1

/-- The structure morphism from the spectrum of the carrier. -/
def toS (R : CompleteLocalSAlgebra S) : Spec (CommRingCat.of R.carrier) ⟶ S := R.2.2.2.2.1

/-- The spectrum of a Noetherian complete local `S`-algebra is locally Noetherian. -/
instance instIsLocallyNoetherian_toS (R : CompleteLocalSAlgebra S) :
    AlgebraicGeometry.IsLocallyNoetherian (Over.mk R.toS).left := by
  change IsLocallyNoetherian (Spec (CommRingCat.of R.carrier))
  infer_instance

/-- The residue field is locally of finite type over the base scheme. -/
theorem residue_locallyOfFiniteType (R : CompleteLocalSAlgebra S) :
    LocallyOfFiniteType
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (maximalIdeal R.carrier))) ≫ R.toS) :=
  R.2.2.2.2.2


/-- Package a Noetherian complete local ring with a structure morphism to `S` whose
residue field is of finite type over `S`. -/
def of (R : Type u) [CommRing R] [IsNoetherianRing R]
    [IsCompleteLocalRing R] (toS : Spec (CommRingCat.of R) ⟶ S)
    (h : LocallyOfFiniteType
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (maximalIdeal R))) ≫ toS)) :
    CompleteLocalSAlgebra S :=
  ⟨CommRingCat.of R, inferInstance, inferInstance, inferInstance, toS, h⟩

/-- The packaged complete local `S`-algebra recovers the supplied carrier. -/
theorem of_carrier (R : Type u) [CommRing R] [IsNoetherianRing R]
    [IsCompleteLocalRing R] (toS : Spec (CommRingCat.of R) ⟶ S)
    (h : LocallyOfFiniteType
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (maximalIdeal R))) ≫ toS)) :
    (of R toS h).carrier = R := rfl

/-- `CompleteLocalSAlgebra.of` recovers the supplied carrier and structure morphism. -/
theorem spec (R : Type u) [CommRing R] [IsNoetherianRing R]
    [IsCompleteLocalRing R] (toS : Spec (CommRingCat.of R) ⟶ S)
    (h : LocallyOfFiniteType
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (maximalIdeal R))) ≫ toS)) :
    (of R toS h).carrier = R ∧ (of R toS h).toS = toS := ⟨rfl, rfl⟩

/-- The positive maximal-adic quotient ring `R ⧸ m^{n+1}`. -/
abbrev truncationRing (R : CompleteLocalSAlgebra S) (n : ℕ) : CommRingCat.{u} :=
  .of (R.carrier ⧸ maximalIdeal R.carrier ^ (n + 1))

/-- Spectrum of the `n`th maximal-adic truncation, `Spec(R ⧸ m^{n+1})`. -/
def truncationSpec (R : CompleteLocalSAlgebra S) (n : ℕ) : Scheme.{u} :=
  Spec (R.truncationRing n)

/-- Canonical first-order thickening `Spec(R ⧸ m^{n+1}) ⟶ Spec(R ⧸ m^{n+2})`. -/
def truncationMap (R : CompleteLocalSAlgebra S) (n : ℕ) :
    R.truncationSpec n ⟶ R.truncationSpec (n + 1) :=
  Spec.map (CommRingCat.ofHom
    (Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_succ (n + 1)))))

/-- Structure morphism `Spec(R ⧸ m^{n+1}) ⟶ S` of a truncation. -/
def truncationToS (R : CompleteLocalSAlgebra S) (n : ℕ) : R.truncationSpec n ⟶ S :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (maximalIdeal R.carrier ^ (n + 1)))) ≫
    R.toS

/-- Each maximal-adic truncation `Spec(R ⧸ m^{n+1})` is locally Noetherian. -/
instance instIsLocallyNoetherian_truncationToS (R : CompleteLocalSAlgebra S)
    (n : ℕ) :
    AlgebraicGeometry.IsLocallyNoetherian (Over.mk (R.truncationToS n)).left := by
  change IsLocallyNoetherian (Spec (R.truncationRing n))
  unfold truncationRing
  infer_instance

/-- Successive truncation morphisms are compatible with the structure maps to `S`. -/
theorem stageToS_comp (R : CompleteLocalSAlgebra S) (n : ℕ) :
    R.truncationMap n ≫ R.truncationToS (n + 1) = R.truncationToS n := by
  unfold truncationMap truncationToS truncationSpec truncationRing
  rw [← Category.assoc, ← Spec.map_comp]
  rfl

/-- The object `Spec(R ⧸ m^{n+1}) ⟶ S` of `Over S` at stage `n`. -/
def stageOver (R : CompleteLocalSAlgebra S) (n : ℕ) : Over S :=
  Over.mk (R.truncationToS n)

/-- The underlying scheme of each maximal-adic stage over `S` is locally Noetherian. -/
instance instIsLocallyNoetherian_stageOver (R : CompleteLocalSAlgebra S)
    (n : ℕ) :
    AlgebraicGeometry.IsLocallyNoetherian (R.stageOver n).left := by
  change IsLocallyNoetherian (Over.mk (R.truncationToS n)).left
  exact instIsLocallyNoetherian_truncationToS R n

/-- The morphism `Spec(R ⧸ m^{n+1}) ⟶ Spec(R ⧸ m^{n+2})` in `Over S`. -/
def stageHom (R : CompleteLocalSAlgebra S) (n : ℕ) :
    R.stageOver n ⟶ R.stageOver (n + 1) :=
  Over.homMk (R.truncationMap n) (R.stageToS_comp n)

/-- Canonical scheme morphism `Spec(R ⧸ m^{n+1}) ⟶ Spec(R)`. -/
def truncationToSpec (R : CompleteLocalSAlgebra S) (n : ℕ) :
    R.truncationSpec n ⟶ Spec (CommRingCat.of R.carrier) :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (maximalIdeal R.carrier ^ (n + 1))))

/-- `truncationToSpec` is the spectrum of the quotient map of `m^{n+1}`. -/
theorem truncationToSpec_eq (R : CompleteLocalSAlgebra S) (n : ℕ) :
    R.truncationToSpec n =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (maximalIdeal R.carrier ^ (n + 1)))) := rfl

/-- Restriction morphism `Spec(R ⧸ m^{n+1}) ⟶ Spec(R)` in `Over S`. -/
def truncationOverHom (R : CompleteLocalSAlgebra S) (n : ℕ) :
    R.stageOver n ⟶ Over.mk R.toS :=
  Over.homMk (R.truncationToSpec n) rfl

/-- The underlying scheme morphism of `truncationOverHom` is `truncationToSpec`. -/
theorem truncationOverHom_left (R : CompleteLocalSAlgebra S) (n : ℕ) :
    (R.truncationOverHom n).left = R.truncationToSpec n := rfl

/-- Restriction to stage `n` factors through the successor thickening
`Spec(R ⧸ m^{n+1}) ⟶ Spec(R ⧸ m^{n+2}) ⟶ Spec(R)`. -/
theorem truncationOverHom_comp (R : CompleteLocalSAlgebra S) (n : ℕ) :
    R.truncationOverHom n = R.stageHom n ≫ R.truncationOverHom (n + 1) := by
  apply Over.OverMorphism.ext
  change R.truncationToSpec n = R.truncationMap n ≫ R.truncationToSpec (n + 1)
  unfold truncationToSpec truncationMap
  exact Spec.map_comp
    (CommRingCat.ofHom (Ideal.Quotient.mk (maximalIdeal R.carrier ^ (n + 1 + 1))))
    (CommRingCat.ofHom (Ideal.Quotient.factor
      (S := maximalIdeal R.carrier ^ (n + 1 + 1))
      (T := maximalIdeal R.carrier ^ (n + 1))
      (Ideal.pow_le_pow_right (Nat.le_succ (n + 1)))))

end CompleteLocalSAlgebra

end AlgebraicGeometry
