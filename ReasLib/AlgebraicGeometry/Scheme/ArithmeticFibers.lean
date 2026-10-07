module

public import Mathlib.Algebra.Field.ZMod
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.Data.Nat.Prime.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

namespace AlgebraicGeometry

/-- The canonical morphism `Spec (ZMod p) ⟶ Spec ℤ` induced by `Int.castRingHom (ZMod p)`. -/
def specZModToSpecInt (p : ℕ) :
    Spec (CommRingCat.of (ZMod p)) ⟶ Spec (CommRingCat.of ℤ) :=
  Spec.map (CommRingCat.ofHom (Int.castRingHom (ZMod p)))

/-- The canonical morphism `Spec ℚ ⟶ Spec ℤ` induced by `algebraMap ℤ ℚ`. -/
def specRatToSpecInt :
    Spec (CommRingCat.of ℚ) ⟶ Spec (CommRingCat.of ℤ) :=
  Spec.map (CommRingCat.ofHom (algebraMap ℤ ℚ))

/-- If a finite-type morphism to `Spec ℤ` has nonempty fibers over infinitely many prime
residue fields, then its generic fiber over `Spec ℚ` is nonempty. -/
theorem nonempty_pullback_specRat_of_infinite_nonempty_pullback_specZMod
    {X : Scheme} (f : X ⟶ Spec (CommRingCat.of ℤ)) [Scheme.Hom.FiniteType f]
    (h : {p : ℕ | p.Prime ∧
        Nonempty (pullback f (specZModToSpecInt p) : Scheme)}.Infinite) :
    Nonempty (pullback f specRatToSpecInt : Scheme) := sorry

/-- The coproduct of `Spec (ZMod p)` over all primes `p`, as a scheme over `Spec ℤ`. -/
def sigmaSpecZMod : Scheme :=
  ∐ fun p : Nat.Primes ↦ Spec (CommRingCat.of (ZMod (p : ℕ)))

/-- The structure morphism `sigmaSpecZMod ⟶ Spec ℤ` obtained by descending the family
`specZModToSpecInt`. -/
def sigmaSpecZModToSpecInt : sigmaSpecZMod ⟶ Spec (CommRingCat.of ℤ) :=
  Sigma.desc fun p : Nat.Primes ↦ specZModToSpecInt (p : ℕ)

/-- The coproduct morphism `sigmaSpecZModToSpecInt` is locally of finite type. -/
instance instLocallyOfFiniteTypeSigmaSpecZModToSpecInt :
    LocallyOfFiniteType sigmaSpecZModToSpecInt := sorry

/-- The coproduct morphism `sigmaSpecZModToSpecInt` is not of finite type. -/
theorem sigmaSpecZModToSpecInt_not_finiteType :
    ¬ Scheme.Hom.FiniteType sigmaSpecZModToSpecInt := sorry

/-- For infinitely many primes `p`, the fiber product of `sigmaSpecZMod` with `Spec (ZMod p)`
over `Spec ℤ` is nonempty. -/
theorem infinite_nonempty_pullback_specZMod_sigmaSpecZModToSpecInt :
    {p : ℕ | p.Prime ∧
        Nonempty (pullback sigmaSpecZModToSpecInt (specZModToSpecInt p) :
          Scheme)}.Infinite := sorry

/-- The fiber product of `sigmaSpecZMod` with `Spec ℚ` over `Spec ℤ` is empty. -/
theorem isEmpty_pullback_specRat_sigmaSpecZModToSpecInt :
    IsEmpty (pullback sigmaSpecZModToSpecInt specRatToSpecInt : Scheme) := sorry

/-- There is a locally finite-type morphism to `Spec ℤ` with nonempty fibers over infinitely
many prime residue fields and empty generic fiber. -/
theorem exists_locallyOfFiniteType_counterexample :
    ∃ (X : Scheme) (f : X ⟶ Spec (CommRingCat.of ℤ)),
      LocallyOfFiniteType f ∧
        {p : ℕ | p.Prime ∧
            Nonempty (pullback f (specZModToSpecInt p) : Scheme)}.Infinite ∧
          IsEmpty (pullback f specRatToSpecInt : Scheme) := sorry

end AlgebraicGeometry
