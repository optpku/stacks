/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.IdealPowerTorsion.Forward

/-!
Canonical-source DATA leaf for the reverse direction of the strict positive quotient tower.

The source diagram is the actual `strictDiagram` from the forward DATA leaf. A torsion
coordinate is given an annihilation exponent, descended through the actual quotient
`A / I^(n+1)` by `fromAnnihilated`, inserted into the actual single-source Hom
complex by `Cochain.fromSingleMk`, and (when a colimit instance is supplied) sent
through the actual categorical leg `colimit.ι`.

This file deliberately stops at the concrete representative/section data. The
choice is made only from a true primary-component membership witness. It does not
choose an `IsColimit`, a desired inverse, or a `Nonempty` witness. The remaining
independence, linearity, and all-degree differential laws are propositions and are
listed as explicit debt below; no non-Prop data is hidden behind `sorry`.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits
open CochainComplex.HomComplex

namespace CochainComplex.IdealPowerTorsion.StrictColimitReverseData

open CochainComplex.IdealPowerTorsion

variable {A : Type u} [CommRing A]

/-- The ambient value of a degree-`q` element of the specified primary component. -/
def ambientValue (I : Ideal A) (J : CochainComplex (ModuleCat.{u} A) ℤ) (q : ℤ)
    (x : (gamma I J).X q) : J.X q :=
  (gammaTermInclusion I J q).hom x

/--
A true torsion-membership witness in exactly the positive exponent convention used
by `quotientStage I n = A / I^(n+1)`. The proof is Prop debt only: unfold the
actual primary-component membership criterion, rewrite
`Submodule.mem_torsionBySet_iff`, and increase an arbitrary witness to the positive
stage convention when necessary.
-/
theorem exists_annihilation_exponent
    (I : Ideal A) (J : CochainComplex (ModuleCat.{u} A) ℤ) (q : ℤ)
    (x : (gamma I J).X q) :
    ∃ n : ℕ, ∀ a ∈ I ^ (n + 1), a • ambientValue I J q x = 0 := by
  let y := (gammaTermIso I J q).hom.hom x
  obtain ⟨n, hn⟩ :=
    (Ideal.primaryComponent_mem (I := I) (M := J.X q) (x := (y : J.X q))).mp y.property
  have hn' : ∀ a ∈ I ^ n, a • (y : J.X q) = 0 := by
    simpa only [Submodule.mem_torsionBySet_iff, SetLike.coe_sort_coe, Subtype.forall] using hn
  refine ⟨n, ?_⟩
  intro a ha
  change a • (y : J.X q) = 0
  exact hn' a (Ideal.pow_le_pow_right (Nat.le_succ n) ha)

/-- The only choice made by this DATA: an exponent selected from true torsion membership. -/
noncomputable def chosenExponent
    (I : Ideal A) (J : CochainComplex (ModuleCat.{u} A) ℤ) (q : ℤ)
    (x : (gamma I J).X q) : ℕ :=
  Classical.choose (exists_annihilation_exponent I J q x)

@[simp]
theorem chosenExponent_spec
    (I : Ideal A) (J : CochainComplex (ModuleCat.{u} A) ℤ) (q : ℤ)
    (x : (gamma I J).X q) :
    ∀ a ∈ I ^ (chosenExponent I J q x + 1),
      a • ambientValue I J q x = 0 :=
  Classical.choose_spec (exists_annihilation_exponent I J q x)

/-- The actual quotient map supplied to the quotient descent API. -/
def quotientLift
    (I : Ideal A) (J : CochainComplex (ModuleCat.{u} A) ℤ) (q : ℤ)
    (n : ℕ) (x : (gamma I J).X q)
    (hx : ∀ a ∈ I ^ (n + 1), a • ambientValue I J q x = 0) :
    quotientStage I n →ₗ[A] J.X q :=
  fromAnnihilated I n (J.X q) (ambientValue I J q x) hx

/--
The genuine degree-`q` stage element. The source is concentrated in degree zero,
so the element is the existing `fromSingleMk` of the actual quotient lift.
-/
def stageLift
    (I : Ideal A) (J : CochainComplex (ModuleCat.{u} A) ℤ) (q : ℤ)
    (n : ℕ) (x : (gamma I J).X q)
    (hx : ∀ a ∈ I ^ (n + 1), a • ambientValue I J q x = 0) :
    (strictStage I J n).X q :=
  Cochain.fromSingleMk
    (ModuleCat.ofHom (quotientLift I J q n x hx))
    (zero_add q)

@[simp]
theorem stageLift_read
    (I : Ideal A) (J : CochainComplex (ModuleCat.{u} A) ℤ) (q : ℤ)
    (n : ℕ) (x : (gamma I J).X q)
    (hx : ∀ a ∈ I ^ (n + 1), a • ambientValue I J q x = 0) :
    singleRead I J n q (stageLift I J q n x hx) = quotientLift I J q n x hx := by
  simpa [stageLift] using
    (singleRead_fromSingleMk I J n q
      (ModuleCat.ofHom (quotientLift I J q n x hx)))

/-- Evaluation at `[1]` recovers the chosen ambient torsion element. -/
theorem stageLift_evaluates
    (I : Ideal A) (J : CochainComplex (ModuleCat.{u} A) ℤ) (q : ℤ)
    (n : ℕ) (x : (gamma I J).X q)
    (hx : ∀ a ∈ I ^ (n + 1), a • ambientValue I J q x = 0) :
    (gammaTermInclusion I J q).hom
        (evalTerm I J n q (stageLift I J q n x hx)) =
      ambientValue I J q x := by
  rw [evalTerm_coe, stageLift_read]
  change evalOneLinear I n (J.X q)
    (fromAnnihilated I n (J.X q) (ambientValue I J q x) hx) = ambientValue I J q x
  exact evalOne_fromAnnihilated I n (J.X q) (ambientValue I J q x) hx

/-- Transport a stage element through the identity-on-stage iso used by the sequence functor. -/
def diagramStageLift
    (I : Ideal A) (J : CochainComplex (ModuleCat.{u} A) ℤ) (q : ℤ)
    (n : ℕ) (x : (gamma I J).X q)
    (hx : ∀ a ∈ I ^ (n + 1), a • ambientValue I J q x = 0) :
    ((strictDiagram I J).obj n).X q :=
  ((strictDiagramObjIso I J n).inv.f q).hom (stageLift I J q n x hx)

/-- The chosen stage lift, with all proof arguments supplied by the chosen witness. -/
noncomputable def chosenDiagramStageLift
    (I : Ideal A) (J : CochainComplex (ModuleCat.{u} A) ℤ) (q : ℤ)
    (x : (gamma I J).X q) :
    ((strictDiagram I J).obj (chosenExponent I J q x)).X q :=
  diagramStageLift I J q (chosenExponent I J q x) x
    (chosenExponent_spec I J q x)

section Colimit

variable (I : Ideal A) (J : CochainComplex (ModuleCat.{u} A) ℤ)
variable [HasColimit (strictDiagram I J)]

/-- The actual categorical colimit injection at a specified finite stage. -/
noncomputable def colimitInjection (n : ℕ) :
    (strictDiagram I J).obj n ⟶ colimit (strictDiagram I J) :=
  colimit.ι (strictDiagram I J) n

/-- A concrete colimit representative of a torsion coordinate. -/
noncomputable def colimitRepresentative (q : ℤ) (x : (gamma I J).X q) :
    (colimit (strictDiagram I J)).X q :=
  ((colimitInjection I J (chosenExponent I J q x)).f q).hom
    (chosenDiagramStageLift I J q x)

/-- The same representative made from any supplied true annihilation witness. -/
noncomputable def colimitRepresentativeOfWitness
    (q : ℤ) (n : ℕ) (x : (gamma I J).X q)
    (hx : ∀ a ∈ I ^ (n + 1), a • ambientValue I J q x = 0) :
    (colimit (strictDiagram I J)).X q :=
  ((colimitInjection I J n).f q).hom (diagramStageLift I J q n x hx)

/--
Independence of the exponent witness. This is a true Prop law, intentionally
admitted here: choose a common `max` stage, use the finite composite supplied by
`Functor.ofSequence`, apply `fromAnnihilated_class` on quotient classes, and close
with `colimit.w`. No map is chosen by this proposition.
-/
theorem colimitRepresentative_independent
    (q : ℤ) (x : (gamma I J).X q) (n : ℕ)
    (hx : ∀ a ∈ I ^ (n + 1), a • ambientValue I J q x = 0) :
    colimitRepresentative I J q x =
      colimitRepresentativeOfWitness I J q n x hx := by
  sorry

/--
The canonical evaluation map induced by the specified DATA cocone. This uses
Mathlib's existing colimit object and `colimit.desc`; it does not assert that the
cocone is colimiting.
-/
noncomputable def colimitEvaluation :
    colimit (strictDiagram I J) ⟶ gamma I J :=
  colimit.desc (strictDiagram I J) (torsionCocone I J)

@[reassoc (attr := simp)]
theorem colimitEvaluation_ι (n : ℕ) :
    colimitInjection I J n ≫ colimitEvaluation I J =
      (torsionCocone I J).ι.app n := by
  change
    colimit.ι (strictDiagram I J) n ≫
        colimit.desc (strictDiagram I J) (torsionCocone I J) =
      (torsionCocone I J).ι.app n
  exact colimit.ι_desc (torsionCocone I J) n

/--
The concrete representative is sent back to the original gamma element. This is
true Prop debt only: use `colimitEvaluation_ι`, the stage evaluation formula, and
the already established injectivity of `gammaTermInclusion`.
-/
theorem colimitEvaluation_colimitRepresentative
    (q : ℤ) (x : (gamma I J).X q) :
    ((colimitEvaluation I J).f q).hom (colimitRepresentative I J q x) = x := by
  sorry

end Colimit

end CochainComplex.IdealPowerTorsion.StrictColimitReverseData

end
