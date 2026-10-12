/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap30.Lemma_30_20_3_Comparison
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Ideal.PowerQuotient.Module
public import ReasLib.AlgebraicGeometry.Scheme.Module.RingedSpace
public import ReasLib.CategoryTheory.InverseSystem.MittagLeffler

/-!
# Ideal-power quotient cohomology over an affine base

This module packages the inverse system `H^p(X, F / I^n F)` and the three
stabilization clauses of Stacks tag 02OB.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Scheme.Modules
open SheafOfModules.RingedSite.IdealSheaf

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom.IdealPowerCohomology.Quotient

variable {A : Type u} [CommRing A]
variable {X : Scheme.{u}}
variable [HasExt (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u})]

/-- The sheaf `F / I^n F` obtained from the pullback of `I` along `f`. -/
noncomputable abbrev stage (I : Ideal A) (f : X ⟶ Spec (CommRingCat.of A))
    (F : X.Modules) (n : ℕ) : X.Modules :=
  fromRingedSpaceObj X
    (PowerQuotientModule.stage.{u, u, u}
      ((idealSheafDataOfIdealOnSpec I).comap f).toSubobject
      (toRingedSpaceObj X F) n)

/-- Stage `n` is the canonical ideal-power quotient of `F`. -/
theorem stage_eq (I : Ideal A) (f : X ⟶ Spec (CommRingCat.of A))
    (F : X.Modules) (n : ℕ) :
    stage I f F n =
      fromRingedSpaceObj X
        (PowerQuotientModule.stage.{u, u, u}
          ((idealSheafDataOfIdealOnSpec I).comap f).toSubobject
          (toRingedSpaceObj X F) n) := sorry

/-- The canonical projection `F ⟶ F / I^n F`. -/
noncomputable abbrev projection (I : Ideal A) (f : X ⟶ Spec (CommRingCat.of A))
    (F : X.Modules) (n : ℕ) : F ⟶ stage I f F n :=
  fromRingedSpaceMap X
    (PowerQuotientModule.projection.{u, u, u}
      ((idealSheafDataOfIdealOnSpec I).comap f).toSubobject
      (toRingedSpaceObj X F) n)

/-- The named projection is the canonical cokernel projection of the ideal-power action. -/
theorem projection_eq (I : Ideal A) (f : X ⟶ Spec (CommRingCat.of A))
    (F : X.Modules) (n : ℕ) :
    projection I f F n =
      fromRingedSpaceMap X
        (PowerQuotientModule.projection.{u, u, u}
          ((idealSheafDataOfIdealOnSpec I).comap f).toSubobject
          (toRingedSpaceObj X F) n) := sorry

/-- The successor transition `F / I^(n+1) F ⟶ F / I^n F`. -/
noncomputable abbrev step (I : Ideal A) (f : X ⟶ Spec (CommRingCat.of A))
    (F : X.Modules) (n : ℕ) : stage I f F (n + 1) ⟶ stage I f F n :=
  fromRingedSpaceMap X
    (PowerQuotientModule.step.{u, u, u}
      ((idealSheafDataOfIdealOnSpec I).comap f).toSubobject
      (toRingedSpaceObj X F) n)

/-- The named successor is the canonical quotient transition. -/
theorem step_eq (I : Ideal A) (f : X ⟶ Spec (CommRingCat.of A))
    (F : X.Modules) (n : ℕ) :
    step I f F n =
      fromRingedSpaceMap X
        (PowerQuotientModule.step.{u, u, u}
          ((idealSheafDataOfIdealOnSpec I).comap f).toSubobject
          (toRingedSpaceObj X F) n) := sorry

/-- The inverse system `n ↦ F / I^n F` of module sheaves. -/
noncomputable def system (I : Ideal A) (f : X ⟶ Spec (CommRingCat.of A))
    (F : X.Modules) : SequentialInverseSystem X.Modules :=
  Functor.ofOpSequence (step I f F)

/-- The sheaf-level inverse system evaluates to the named quotient stage. -/
theorem system_obj (I : Ideal A) (f : X ⟶ Spec (CommRingCat.of A))
    (F : X.Modules) (n : ℕ) :
    (system I f F).obj (op n) = stage I f F n := sorry

/-- The cohomology object `H^p(X, F / I^n F)` as an `A`-module. -/
noncomputable abbrev cohomology (I : Ideal A) (f : X ⟶ Spec (CommRingCat.of A))
    (F : X.Modules) (p n : ℕ) : ModuleCat A :=
  Hom.cohomology f (stage I f F n) p

/-- Quotient cohomology is affine-base cohomology of the corresponding stage. -/
theorem cohomology_eq (I : Ideal A) (f : X ⟶ Spec (CommRingCat.of A))
    (F : X.Modules) (p n : ℕ) :
    cohomology I f F p n = Hom.cohomology f (stage I f F n) p := sorry

/-- The successor map on `H^p(X, F / I^n F)`. -/
noncomputable def cohomologyStep (I : Ideal A) (f : X ⟶ Spec (CommRingCat.of A))
    (F : X.Modules) (p n : ℕ) :
    cohomology I f F p (n + 1) ⟶ cohomology I f F p n :=
  (Hom.cohomologyFunctor f p).map (step I f F n)

/-- The named successor cohomology map is cohomology of the sheaf-level successor. -/
theorem cohomologyStep_eq (I : Ideal A) (f : X ⟶ Spec (CommRingCat.of A))
    (F : X.Modules) (p n : ℕ) :
    cohomologyStep I f F p n = (Hom.cohomologyFunctor f p).map (step I f F n) := sorry

/-- The inverse system `n ↦ H^p(X, F / I^n F)`. -/
noncomputable def tower (I : Ideal A) (f : X ⟶ Spec (CommRingCat.of A))
    (F : X.Modules) (p : ℕ) : SequentialInverseSystem (ModuleCat A) :=
  system I f F ⋙ Hom.cohomologyFunctor f p

/-- The object at index `n` of the quotient cohomology tower. -/
theorem tower_obj (I : Ideal A) (f : X ⟶ Spec (CommRingCat.of A))
    (F : X.Modules) (p n : ℕ) :
    (tower I f F p).obj (op n) = cohomology I f F p n := sorry

/-- Every successor transition of the quotient cohomology tower is `cohomologyStep`. -/
theorem tower_stepMap (I : Ideal A) (f : X ⟶ Spec (CommRingCat.of A))
    (F : X.Modules) (p n : ℕ) :
    (tower I f F p).stepMap n = cohomologyStep I f F p n := sorry

/-- The canonical transition `H^p(X, F / I^k F) ⟶ H^p(X, F / I^n F)` for `n ≤ k`. -/
noncomputable def transition (I : Ideal A) (f : X ⟶ Spec (CommRingCat.of A))
    (F : X.Modules) (p : ℕ) {n k : ℕ} (h : n ≤ k) :
    cohomology I f F p k ⟶ cohomology I f F p n :=
  (tower I f F p).transitionMap h

/-- Every tower transition is the named quotient-cohomology transition. -/
theorem transition_eq (I : Ideal A) (f : X ⟶ Spec (CommRingCat.of A))
    (F : X.Modules) (p : ℕ) {n k : ℕ} (h : n ≤ k) :
    transition I f F p h = (tower I f F p).transitionMap h := sorry

/-- The canonical map `H^p(X, F) ⟶ H^p(X, F / I^n F)` induced by the quotient projection. -/
noncomputable def toQuotient (I : Ideal A) (f : X ⟶ Spec (CommRingCat.of A))
    (F : X.Modules) (p n : ℕ) :
    Hom.cohomology f F p ⟶ cohomology I f F p n :=
  (Hom.cohomologyFunctor f p).map (projection I f F n)

/-- `toQuotient` is cohomology of the sheaf-level projection. -/
theorem toQuotient_eq (I : Ideal A) (f : X ⟶ Spec (CommRingCat.of A))
    (F : X.Modules) (p n : ℕ) :
    toQuotient I f F p n = (Hom.cohomologyFunctor f p).map (projection I f F n) := sorry

/-- A single exponent `c` witnessing kernel control, Mittag-Leffler, and stable images for
the quotient cohomology tower. -/
structure Stabilization (I : Ideal A) (f : X ⟶ Spec (CommRingCat.of A))
    (F : X.Modules) (p c : ℕ) : Prop where
  /-- Clause (1): kernels of maps to quotient cohomology lie in the stated adic submodule. -/
  ker_le :
    ∀ (n : ℕ), c ≤ n →
      LinearMap.ker (toQuotient I f F p n).hom ≤
        Ideal.PowerSubmodule.stage I (Hom.cohomology f F p) (n - c)
  /-- Clause (2): the inverse system `n ↦ H^p(X, F / I^n F)` is Mittag-Leffler. -/
  isMittagLeffler : (tower I f F p).IsMittagLeffler
  /-- Clause (3): images of late transitions agree with the image from ambient cohomology. -/
  image_eq :
    ∀ (n k : ℕ) (h : n + c ≤ k),
      LinearMap.range (transition I f F p (Nat.le_trans (Nat.le_add_right n c) h)).hom =
        LinearMap.range (toQuotient I f F p n).hom

namespace Stabilization

/-- Package the three quotient-cohomology stabilization clauses at a shared exponent `c`. -/
def ofClauses {I : Ideal A} {f : X ⟶ Spec (CommRingCat.of A)}
    {F : X.Modules} {p c : ℕ}
    (ker_le :
      ∀ (n : ℕ), c ≤ n →
        LinearMap.ker (toQuotient I f F p n).hom ≤
          Ideal.PowerSubmodule.stage I (Hom.cohomology f F p) (n - c))
    (isMittagLeffler : (tower I f F p).IsMittagLeffler)
    (image_eq :
      ∀ (n k : ℕ) (h : n + c ≤ k),
        LinearMap.range (transition I f F p (Nat.le_trans (Nat.le_add_right n c) h)).hom =
          LinearMap.range (toQuotient I f F p n).hom) :
    Stabilization I f F p c where
  ker_le := ker_le
  isMittagLeffler := isMittagLeffler
  image_eq := image_eq

/-- All defining conditions of an affine-base quotient cohomology stabilization, exposed
together. -/
theorem spec {I : Ideal A} {f : X ⟶ Spec (CommRingCat.of A)}
    {F : X.Modules} {p c : ℕ} (D : Stabilization I f F p c) :
    (∀ n, c ≤ n →
        LinearMap.ker (toQuotient I f F p n).hom ≤
          Ideal.PowerSubmodule.stage I (Hom.cohomology f F p) (n - c)) ∧
      (tower I f F p).IsMittagLeffler ∧
      (∀ n k (h : n + c ≤ k),
        LinearMap.range (transition I f F p (Nat.le_trans (Nat.le_add_right n c) h)).hom =
          LinearMap.range (toQuotient I f F p n).hom) := sorry

end Stabilization

section ExistsStabilization

variable [hA : IsNoetherianRing A]

include hA

/-- For a proper morphism to the spectrum of a Noetherian ring and a coherent sheaf, some `c`
witnesses all three quotient-cohomology stabilization clauses. -/
theorem existsStabilization (I : Ideal A)
    (f : X ⟶ Spec (CommRingCat.of A)) [IsProper f]
    (F : X.Modules) [F.IsCoherent] (p : ℕ) :
    ∃ c : ℕ, Stabilization I f F p c := sorry

/-- Some `c` controls kernels of `H^p(X, F) ⟶ H^p(X, F / I^n F)` by `I^(n-c) H^p(X, F)`
for all `n ≥ c`. -/
theorem ker_le (I : Ideal A) (f : X ⟶ Spec (CommRingCat.of A)) [IsProper f]
    (F : X.Modules) [F.IsCoherent] (p : ℕ) :
    ∃ c : ℕ, ∀ n, c ≤ n →
      LinearMap.ker (toQuotient I f F p n).hom ≤
        Ideal.PowerSubmodule.stage I (Hom.cohomology f F p) (n - c) := sorry

/-- The inverse system `n ↦ H^p(X, F / I^n F)` satisfies the Mittag-Leffler condition. -/
theorem isMittagLeffler (I : Ideal A) (f : X ⟶ Spec (CommRingCat.of A)) [IsProper f]
    (F : X.Modules) [F.IsCoherent] (p : ℕ) :
    SequentialInverseSystem.IsMittagLeffler (tower I f F p) := sorry

/-- Some `c` makes images of `H^p(F / I^k F) ⟶ H^p(F / I^n F)` agree with the image from
`H^p(F)` whenever `k ≥ n + c`. -/
theorem image_eq (I : Ideal A) (f : X ⟶ Spec (CommRingCat.of A)) [IsProper f]
    (F : X.Modules) [F.IsCoherent] (p : ℕ) :
    ∃ c : ℕ, ∀ n k (h : n + c ≤ k),
      LinearMap.range (transition I f F p (Nat.le_trans (Nat.le_add_right n c) h)).hom =
        LinearMap.range (toQuotient I f F p n).hom := sorry

end ExistsStabilization

end AlgebraicGeometry.Scheme.Hom.IdealPowerCohomology.Quotient
