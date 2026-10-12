/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.InverseSystem.MittagLeffler
public import stacks_project.Chap69.Lemma_69_22_4_Quotient

/-!
# Inverse systems of ideal-power quotient cohomology

Affine-base cohomology of the quotients `F / I^n F` forms a sequential inverse
system in `ModuleCat A`. Comparison maps from `H^p(X, F)` identify kernels with
ideal-power submodules and eventual images of the tower maps.
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
  GradedCohomology.cohomologyOver (𝟙 (Spec (CommRingCat.of A))) f (quotient I f F n) p

/-- Quotient cohomology is affine-base cohomology of the corresponding quotient sheaf. -/
theorem quotientCohomology_eq (I : Ideal A)
    (f : X ⟶ ofOver (Over.mk (𝟙 (Spec (CommRingCat.of A))))) (F : X.Modules)
    [Abelian X.Modules]
    [Abelian (ofOver (Over.mk (𝟙 (Spec (CommRingCat.of A))))).Modules]
    [HasInjectiveResolutions X.Modules] (p n : ℕ) :
    quotientCohomology I f F p n =
      GradedCohomology.cohomologyOver (𝟙 (Spec (CommRingCat.of A))) f
        (quotient I f F n) p :=
  sorry

/-- Affine-base cohomology of `F / I^n F` carries its `A`-module structure from
`ModuleCat A`. -/
instance module_quotientCohomology (I : Ideal A)
    (f : X ⟶ ofOver (Over.mk (𝟙 (Spec (CommRingCat.of A))))) (F : X.Modules)
    [Abelian X.Modules]
    [Abelian (ofOver (Over.mk (𝟙 (Spec (CommRingCat.of A))))).Modules]
    [HasInjectiveResolutions X.Modules] (p n : ℕ) :
    Module A (quotientCohomology I f F p n) :=
  ModuleCat.isModule (quotientCohomology I f F p n)

/-- Affine-base cohomology of `F / I^n F` is an abelian group via its `ModuleCat`
carrier. -/
instance addCommGroup_quotientCohomology (I : Ideal A)
    (f : X ⟶ ofOver (Over.mk (𝟙 (Spec (CommRingCat.of A))))) (F : X.Modules)
    [Abelian X.Modules]
    [Abelian (ofOver (Over.mk (𝟙 (Spec (CommRingCat.of A))))).Modules]
    [HasInjectiveResolutions X.Modules] (p n : ℕ) :
    AddCommGroup (quotientCohomology I f F p n) :=
  ModuleCat.isAddCommGroup (quotientCohomology I f F p n)

/-- Affine-base cohomology of `F` carries its `A`-module structure from `ModuleCat A`. -/
instance module_cohomologyOver
    (f : X ⟶ ofOver (Over.mk (𝟙 (Spec (CommRingCat.of A))))) (F : X.Modules)
    [Abelian X.Modules]
    [Abelian (ofOver (Over.mk (𝟙 (Spec (CommRingCat.of A))))).Modules]
    [HasInjectiveResolutions X.Modules] (p : ℕ) :
    Module A (GradedCohomology.cohomologyOver (𝟙 (Spec (CommRingCat.of A))) f F p) :=
  ModuleCat.isModule
    (GradedCohomology.cohomologyOver (𝟙 (Spec (CommRingCat.of A))) f F p)

/-- Affine-base cohomology of `F` is an abelian group via its `ModuleCat` carrier. -/
instance addCommGroup_cohomologyOver
    (f : X ⟶ ofOver (Over.mk (𝟙 (Spec (CommRingCat.of A))))) (F : X.Modules)
    [Abelian X.Modules]
    [Abelian (ofOver (Over.mk (𝟙 (Spec (CommRingCat.of A))))).Modules]
    [HasInjectiveResolutions X.Modules] (p : ℕ) :
    AddCommGroup (GradedCohomology.cohomologyOver (𝟙 (Spec (CommRingCat.of A))) f F p) :=
  ModuleCat.isAddCommGroup
    (GradedCohomology.cohomologyOver (𝟙 (Spec (CommRingCat.of A))) f F p)

/-- The comparison map `H^p(X, F) ⟶ H^p(X, F / I^n F)` induced by `quotientMap`. -/
def toQuotientCohomology (I : Ideal A)
    (f : X ⟶ ofOver (Over.mk (𝟙 (Spec (CommRingCat.of A))))) (F : X.Modules)
    [Abelian X.Modules]
    [Abelian (ofOver (Over.mk (𝟙 (Spec (CommRingCat.of A))))).Modules]
    [HasInjectiveResolutions X.Modules] (p n : ℕ) :
    GradedCohomology.cohomologyOver (𝟙 (Spec (CommRingCat.of A))) f F p ⟶
      quotientCohomology I f F p n :=
  GradedCohomology.cohomologyOverMap (𝟙 (Spec (CommRingCat.of A))) f
    (quotientMap I f F n) p

/-- `toQuotientCohomology` is affine-base cohomology of `quotientMap`. -/
theorem toQuotientCohomology_eq (I : Ideal A)
    (f : X ⟶ ofOver (Over.mk (𝟙 (Spec (CommRingCat.of A))))) (F : X.Modules)
    [Abelian X.Modules]
    [Abelian (ofOver (Over.mk (𝟙 (Spec (CommRingCat.of A))))).Modules]
    [HasInjectiveResolutions X.Modules] (p n : ℕ) :
    toQuotientCohomology I f F p n =
      GradedCohomology.cohomologyOverMap (𝟙 (Spec (CommRingCat.of A))) f
        (quotientMap I f F n) p :=
  sorry

/-- The successor map `H^p(X, F / I^(n+1) F) ⟶ H^p(X, F / I^n F)`. -/
def quotientCohomologyStep (I : Ideal A)
    (f : X ⟶ ofOver (Over.mk (𝟙 (Spec (CommRingCat.of A))))) (F : X.Modules)
    [Abelian X.Modules]
    [Abelian (ofOver (Over.mk (𝟙 (Spec (CommRingCat.of A))))).Modules]
    [HasInjectiveResolutions X.Modules] (p n : ℕ) :
    quotientCohomology I f F p (n + 1) ⟶ quotientCohomology I f F p n :=
  GradedCohomology.cohomologyOverMap (𝟙 (Spec (CommRingCat.of A))) f
    (quotientStep I f F n) p

/-- `quotientCohomologyStep` is affine-base cohomology of `quotientStep`. -/
theorem quotientCohomologyStep_eq (I : Ideal A)
    (f : X ⟶ ofOver (Over.mk (𝟙 (Spec (CommRingCat.of A))))) (F : X.Modules)
    [Abelian X.Modules]
    [Abelian (ofOver (Over.mk (𝟙 (Spec (CommRingCat.of A))))).Modules]
    [HasInjectiveResolutions X.Modules] (p n : ℕ) :
    quotientCohomologyStep I f F p n =
      GradedCohomology.cohomologyOverMap (𝟙 (Spec (CommRingCat.of A))) f
        (quotientStep I f F n) p :=
  sorry

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
  sorry

/-- The successor map of `quotientSystem` is `quotientCohomologyStep`. -/
theorem quotientSystem_stepMap (I : Ideal A)
    (f : X ⟶ ofOver (Over.mk (𝟙 (Spec (CommRingCat.of A))))) (F : X.Modules)
    [Abelian X.Modules]
    [Abelian (ofOver (Over.mk (𝟙 (Spec (CommRingCat.of A))))).Modules]
    [HasInjectiveResolutions X.Modules] (p n : ℕ) :
    (quotientSystem I f F p).stepMap n = quotientCohomologyStep I f F p n :=
  sorry

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

/-- In Situation 69.22.1, the kernel of `H^p(X, F) ⟶ H^p(X, F / I^n F)` is contained
in `I^(n-c) H^p(X, F)` for all sufficiently large `n`. -/
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

/-- In Situation 69.22.1, the inverse system `H^p(X, F / I^n F)` is Mittag-Leffler. -/
theorem isMittagLeffler_quotientSystem [IsNoetherianRing A] (I : Ideal A)
    (f : X ⟶ ofOver (Over.mk (𝟙 (Spec (CommRingCat.of A))))) [Proper f]
    (F : X.Modules) [F.IsCoherent]
    [Abelian X.Modules]
    [Abelian (ofOver (Over.mk (𝟙 (Spec (CommRingCat.of A))))).Modules]
    [HasInjectiveResolutions X.Modules] (p : ℕ) :
    IsMittagLeffler (quotientSystem I f F p) :=
  sorry

/-- In Situation 69.22.1, for every `n` the images of
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
