module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.IdealPower.Quotient
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Cohomology.IdealPower.Generation
public import ReasLib.CategoryTheory.InverseSystem.MittagLeffler

/-!
# Inverse systems of ideal-power quotient cohomology

Affine-base cohomology of the quotients `F / I^n F` forms a sequential inverse
system in `ModuleCat A`. Comparison maps from `H^p(X, F)` have kernels bounded
by ideal-power submodules, and their images are the eventual images of the tower maps.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules
open AlgebraicGeometry.AlgebraicSpace.Modules.IdealPowerCohomology
open CategoryTheory CategoryTheory.Limits CategoryTheory.SequentialInverseSystem
open Opposite

noncomputable section

universe u

variable {A : Type u} [CommRing A]
variable {X : AlgebraicSpace (Spec (CommRingCat.of A))}

-- Local instance justification (defeq pin): `HasInjectiveResolutions` and `higherDirectImage` pin the Abelian-induced `Preadditive`/`HasZeroMorphisms` instances for defeq of `cohomologyOver`.
attribute [local instance 2000] Abelian.toPreadditive Preadditive.preadditiveHasZeroMorphisms

namespace AlgebraicGeometry.AlgebraicSpace.Modules.IdealPowerCohomology

/-- Affine-base cohomology `H^p(X, F / I^n F)` as an `A`-module. -/
abbrev quotientCohomology (I : Ideal A)
    (f : X ⟶ ofOver (Over.mk (𝟙 (Spec (CommRingCat.of A))))) (F : X.Modules)
    [Abelian X.Modules]
    [Abelian (ofOver (Over.mk (𝟙 (Spec (CommRingCat.of A))))).Modules]
    [HasInjectiveResolutions X.Modules] (p n : ℕ) : ModuleCat A :=
  GradedCohomology.cohomologyOver (𝟙 (Spec (CommRingCat.of A))) f
    (idealPowerQuotient (pullbackIdeal I f) F n) p

/-- Quotient cohomology is affine-base cohomology of the corresponding quotient sheaf. -/
theorem quotientCohomology_eq (I : Ideal A)
    (f : X ⟶ ofOver (Over.mk (𝟙 (Spec (CommRingCat.of A))))) (F : X.Modules)
    [Abelian X.Modules]
    [Abelian (ofOver (Over.mk (𝟙 (Spec (CommRingCat.of A))))).Modules]
    [HasInjectiveResolutions X.Modules] (p n : ℕ) :
    quotientCohomology I f F p n =
      GradedCohomology.cohomologyOver (𝟙 (Spec (CommRingCat.of A))) f
        (idealPowerQuotient (pullbackIdeal I f) F n) p :=
  rfl

/-- The comparison map `H^p(X, F) ⟶ H^p(X, F / I^n F)` induced by the canonical
quotient projection. -/
def toQuotientCohomology (I : Ideal A)
    (f : X ⟶ ofOver (Over.mk (𝟙 (Spec (CommRingCat.of A))))) (F : X.Modules)
    [Abelian X.Modules]
    [Abelian (ofOver (Over.mk (𝟙 (Spec (CommRingCat.of A))))).Modules]
    [HasInjectiveResolutions X.Modules] (p n : ℕ) :
    GradedCohomology.cohomologyOver (𝟙 (Spec (CommRingCat.of A))) f F p ⟶
      quotientCohomology I f F p n :=
  GradedCohomology.cohomologyOverMap (𝟙 (Spec (CommRingCat.of A))) f
    (idealPowerQuotient.projection (pullbackIdeal I f) F n) p

/-- The comparison map is affine-base cohomology of the canonical quotient projection. -/
theorem toQuotientCohomology_eq (I : Ideal A)
    (f : X ⟶ ofOver (Over.mk (𝟙 (Spec (CommRingCat.of A))))) (F : X.Modules)
    [Abelian X.Modules]
    [Abelian (ofOver (Over.mk (𝟙 (Spec (CommRingCat.of A))))).Modules]
    [HasInjectiveResolutions X.Modules] (p n : ℕ) :
    toQuotientCohomology I f F p n =
      GradedCohomology.cohomologyOverMap (𝟙 (Spec (CommRingCat.of A))) f
        (idealPowerQuotient.projection (pullbackIdeal I f) F n) p :=
  rfl

/-- The successor map `H^p(X, F / I^(n+1) F) ⟶ H^p(X, F / I^n F)`. -/
def quotientCohomologyStep (I : Ideal A)
    (f : X ⟶ ofOver (Over.mk (𝟙 (Spec (CommRingCat.of A))))) (F : X.Modules)
    [Abelian X.Modules]
    [Abelian (ofOver (Over.mk (𝟙 (Spec (CommRingCat.of A))))).Modules]
    [HasInjectiveResolutions X.Modules] (p n : ℕ) :
    quotientCohomology I f F p (n + 1) ⟶ quotientCohomology I f F p n :=
  GradedCohomology.cohomologyOverMap (𝟙 (Spec (CommRingCat.of A))) f
    (idealPowerQuotient.step (pullbackIdeal I f) F n) p

/-- The cohomological successor map is induced by the canonical quotient transition. -/
theorem quotientCohomologyStep_eq (I : Ideal A)
    (f : X ⟶ ofOver (Over.mk (𝟙 (Spec (CommRingCat.of A))))) (F : X.Modules)
    [Abelian X.Modules]
    [Abelian (ofOver (Over.mk (𝟙 (Spec (CommRingCat.of A))))).Modules]
    [HasInjectiveResolutions X.Modules] (p n : ℕ) :
    quotientCohomologyStep I f F p n =
      GradedCohomology.cohomologyOverMap (𝟙 (Spec (CommRingCat.of A))) f
        (idealPowerQuotient.step (pullbackIdeal I f) F n) p :=
  rfl

/-- The inverse system `n ↦ H^p(X, F / I^n F)` in `ModuleCat A`. -/
def quotientSystem (I : Ideal A)
    (f : X ⟶ ofOver (Over.mk (𝟙 (Spec (CommRingCat.of A))))) (F : X.Modules)
    [Abelian X.Modules]
    [Abelian (ofOver (Over.mk (𝟙 (Spec (CommRingCat.of A))))).Modules]
    [HasInjectiveResolutions X.Modules] (p : ℕ) :
    SequentialInverseSystem (ModuleCat A) :=
  Functor.ofOpSequence (fun n ↦ quotientCohomologyStep I f F p n)

/-- Stage `n` of `quotientSystem` is `H^p(X, F / I^n F)`. -/
theorem quotientSystem_obj (I : Ideal A)
    (f : X ⟶ ofOver (Over.mk (𝟙 (Spec (CommRingCat.of A))))) (F : X.Modules)
    [Abelian X.Modules]
    [Abelian (ofOver (Over.mk (𝟙 (Spec (CommRingCat.of A))))).Modules]
    [HasInjectiveResolutions X.Modules] (p n : ℕ) :
    (quotientSystem I f F p).obj (op n) = quotientCohomology I f F p n :=
  rfl

/-- The successor map of `quotientSystem` is `quotientCohomologyStep`. -/
theorem quotientSystem_stepMap (I : Ideal A)
    (f : X ⟶ ofOver (Over.mk (𝟙 (Spec (CommRingCat.of A))))) (F : X.Modules)
    [Abelian X.Modules]
    [Abelian (ofOver (Over.mk (𝟙 (Spec (CommRingCat.of A))))).Modules]
    [HasInjectiveResolutions X.Modules] (p n : ℕ) :
    (quotientSystem I f F p).stepMap n = quotientCohomologyStep I f F p n :=
  Functor.ofOpSequence_map_homOfLE_succ (fun n ↦ quotientCohomologyStep I f F p n) n

/-- Comparison maps from `H^p(X, F)` are natural with respect to the inverse-system
transitions. -/
theorem toQuotientCohomology_natural (I : Ideal A)
    (f : X ⟶ ofOver (Over.mk (𝟙 (Spec (CommRingCat.of A))))) (F : X.Modules)
    [Abelian X.Modules]
    [Abelian (ofOver (Over.mk (𝟙 (Spec (CommRingCat.of A))))).Modules]
    [HasInjectiveResolutions X.Modules] (p : ℕ) {m n : ℕ} (h : m ≤ n) :
    toQuotientCohomology I f F p n ≫ (quotientSystem I f F p).transitionMap h =
      toQuotientCohomology I f F p m :=
  sorry

/-- For a coherent module on an algebraic space proper over a Noetherian affine base,
the kernel of `H^p(X, F) ⟶ H^p(X, F / I^n F)` is contained in
`I^(n-c) H^p(X, F)` for all sufficiently large `n`. -/
theorem exists_ker_le_pow [IsNoetherianRing A] (I : Ideal A)
    (f : X ⟶ ofOver (Over.mk (𝟙 (Spec (CommRingCat.of A))))) [Proper f]
    (F : X.Modules) [F.IsCoherent]
    [Abelian X.Modules]
    [Abelian (ofOver (Over.mk (𝟙 (Spec (CommRingCat.of A))))).Modules]
    [HasInjectiveResolutions X.Modules] (p : ℕ) :
    ∃ c : ℕ, ∀ (n : ℕ), c ≤ n →
      LinearMap.ker (toQuotientCohomology I f F p n).hom ≤
        Ideal.PowerSubmodule.stage I
          (GradedCohomology.cohomologyOver (𝟙 (Spec (CommRingCat.of A))) f F p)
          (n - c) :=
  sorry

/-- For a coherent module on an algebraic space proper over a Noetherian affine base,
the inverse system `H^p(X, F / I^n F)` is Mittag-Leffler. -/
theorem isMittagLeffler_quotientSystem [IsNoetherianRing A] (I : Ideal A)
    (f : X ⟶ ofOver (Over.mk (𝟙 (Spec (CommRingCat.of A))))) [Proper f]
    (F : X.Modules) [F.IsCoherent]
    [Abelian X.Modules]
    [Abelian (ofOver (Over.mk (𝟙 (Spec (CommRingCat.of A))))).Modules]
    [HasInjectiveResolutions X.Modules] (p : ℕ) :
    IsMittagLeffler (quotientSystem I f F p) :=
  sorry

/-- For a coherent module on an algebraic space proper over a Noetherian affine base,
for every `n` the images of
`H^p(X, F / I^k F) ⟶ H^p(X, F / I^n F)` stabilize to the image of
`H^p(X, F) ⟶ H^p(X, F / I^n F)` for all sufficiently large `k ≥ n`. -/
theorem exists_range_eq_toQuotient [IsNoetherianRing A] (I : Ideal A)
    (f : X ⟶ ofOver (Over.mk (𝟙 (Spec (CommRingCat.of A))))) [Proper f]
    (F : X.Modules) [F.IsCoherent]
    [Abelian X.Modules]
    [Abelian (ofOver (Over.mk (𝟙 (Spec (CommRingCat.of A))))).Modules]
    [HasInjectiveResolutions X.Modules] (p : ℕ) :
    ∀ n : ℕ, ∃ (c : ℕ) (hc : n ≤ c),
      ∀ (k : ℕ) (hk : c ≤ k),
        LinearMap.range ((quotientSystem I f F p).transitionMap (hc.trans hk)).hom =
          LinearMap.range (toQuotientCohomology I f F p n).hom :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules.IdealPowerCohomology
