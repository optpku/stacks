/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Homology.Homotopy
public import Mathlib.RingTheory.Noetherian.Defs
public import ReasLib.RingTheory.AdicCompletion.NaiveCotangent.BaseChange.Presentation

/-!
# Canonical chain map of completed naive cotangent complexes under pair base change

Scalar extension of `NL_{B1/A1}^∧` along `B1 → (B1 ⊗[A1] A2)^∧`, followed by
the Jacobian/conormal comparison attached to a same-variable presentation of
the completed base change, yields a chain map
`NL_{B1/A1}^∧ ⊗_{B1} B2 ⟶ NL_{B2/A2}^∧`.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory
open Algebra.Extension
open Algebra.NaiveCotangent.Adic
open Algebra.TopologicallyFiniteType
open CommAlgCat.TopologicallyFiniteType (includeLeftToCompletion)

namespace Algebra.NaiveCotangent.Adic

namespace BaseChange

variable {A1 A2 B1 ι : Type u}
variable [CommRing A1] [CommRing A2] [Algebra A1 A2] [CommRing B1] [Algebra A1 B1]

/-- Coordinatewise application of `includeLeftToCompletion`, as a morphism into
the restriction of scalars of `ι → (B1 ⊗[A1] A2)^∧`. -/
def onVars (I2 : Ideal A2) :
    ModuleCat.of B1 (ι → B1) ⟶
      (ModuleCat.restrictScalars
          (algebraMap B1 (completedBaseChange A1 I2 B1))).obj
        (ModuleCat.of (completedBaseChange A1 I2 B1)
          (ι → completedBaseChange A1 I2 B1)) :=
  ModuleCat.ofHom
    (Y := (ModuleCat.restrictScalars
      (algebraMap B1 (completedBaseChange A1 I2 B1))).obj
        (ModuleCat.of (completedBaseChange A1 I2 B1)
          (ι → completedBaseChange A1 I2 B1)))
    { toFun := fun dx i => includeLeftToCompletion I2 B1 (dx i)
      map_add' := by
        intro dx dy
        funext i
        exact map_add (includeLeftToCompletion I2 B1) (dx i) (dy i)
      map_smul' := by
        intro b dx
        funext i
        exact map_mul (includeLeftToCompletion I2 B1) b (dx i) }

/-- `onVars` applies `includeLeftToCompletion` coordinatewise. -/
theorem onVars_apply (I2 : Ideal A2) (dx : ι → B1) (i : ι) :
    (onVars I2).hom dx i =
      (includeLeftToCompletion I2 B1 : B1 →+* completedBaseChange A1 I2 B1) (dx i) :=
  sorry

/-- The scalar extension `NL_{B1/A1}^∧ ⊗_{B1} (B1 ⊗[A1] A2)^∧` of a completed
naive cotangent complex. -/
def scalarExtension (I1 : Ideal A1) (I2 : Ideal A2)
    [Algebra.TopologicallyFiniteType I1 B1] [Fintype ι]
    (P : Presentation A1 B1 I1 ι) :
    ChainComplex (ModuleCat (completedBaseChange A1 I2 B1)) ℕ :=
  ((ModuleCat.extendScalars
        (algebraMap B1 (completedBaseChange A1 I2 B1))).mapHomologicalComplex
      (ComplexShape.down ℕ)).obj
    (naiveCotangent I1 P)

/-- The differential of `NL_{B1/A1}^∧ ⊗_{B1} B2` in degrees `1 → 0` is the
scalar extension of the Jacobian of `P`. -/
theorem scalarExtension_d_one_zero (I1 : Ideal A1) (I2 : Ideal A2)
    [Algebra.TopologicallyFiniteType I1 B1] [Fintype ι]
    (P : Presentation A1 B1 I1 ι) :
    (scalarExtension I1 I2 P).d 1 0 =
      (ModuleCat.extendScalars
          (algebraMap B1 (completedBaseChange A1 I2 B1))).map
        ((naiveCotangent I1 P).d 1 0) := sorry

/-- The degree-zero component of the canonical comparison, as the adjunct of
`onVars`. -/
def chainMapZero (I1 : Ideal A1) (I2 : Ideal A2)
    [Algebra.TopologicallyFiniteType I1 B1] [Fintype ι]
    (P : Presentation A1 B1 I1 ι) :
    (scalarExtension I1 I2 P).X 0 ⟶
      ModuleCat.of (completedBaseChange A1 I2 B1)
        (ι → completedBaseChange A1 I2 B1) :=
  ((ModuleCat.extendRestrictScalarsAdj
        (algebraMap B1 (completedBaseChange A1 I2 B1))).homEquiv _ _).symm
    (onVars I2)

/-- Scalar extension of the finite coordinate module gives a bijective
    degree-zero comparison map. -/
theorem chainMapZero_bijective (I1 : Ideal A1) (I2 : Ideal A2)
    [IsNoetherianRing A1] [IsNoetherianRing A2]
    [Algebra.TopologicallyFiniteType I1 B1] [Fintype ι]
    (P : Presentation A1 B1 I1 ι) :
    Function.Bijective (chainMapZero I1 I2 P).hom := sorry

variable [IsNoetherianRing A1] [IsNoetherianRing A2]

/-- The degree-one component of the canonical comparison, as the adjunct of
`Cotangent.map toBaseChangeHom`. -/
def chainMapOne (I1 : Ideal A1) (I2 : Ideal A2) {c : ℕ} (hc : 1 ≤ c)
    (hI : I1.map (algebraMap A1 A2) ^ c ≤ I2) (hI2 : I2.FG)
    [Algebra.TopologicallyFiniteType I1 B1] [Fintype ι]
    (P : Presentation A1 B1 I1 ι) :
    (scalarExtension I1 I2 P).X 1 ⟶
      ModuleCat.of (completedBaseChange A1 I2 B1)
        (Presentation.baseChange I1 I2 hc hI hI2 P).toExtension.Cotangent :=
  ((ModuleCat.extendRestrictScalarsAdj
        (algebraMap B1 (completedBaseChange A1 I2 B1))).homEquiv _ _).symm
    (ModuleCat.ofHom (Cotangent.map (Presentation.toBaseChangeHom I1 I2 hc hI hI2 P)))

/-- The canonical chain map
`NL_{B1/A1}^∧ ⊗_{B1} (B1 ⊗[A1] A2)^∧ ⟶ NL_{(B1 ⊗[A1] A2)^∧ / A2}^∧`
induced by coefficient extension of a same-variable presentation. -/
def chainMap (I1 : Ideal A1) (I2 : Ideal A2) {c : ℕ} (hc : 1 ≤ c)
    (hI : I1.map (algebraMap A1 A2) ^ c ≤ I2) (hI2 : I2.FG)
    [Algebra.TopologicallyFiniteType I1 B1] [Fintype ι]
    (P : Presentation A1 B1 I1 ι) :
    scalarExtension I1 I2 P ⟶
      naiveCotangent I2 (Presentation.baseChange I1 I2 hc hI hI2 P) where
  f
    | 0 => chainMapZero I1 I2 P
    | 1 => chainMapOne I1 I2 hc hI hI2 P
    | _ + 2 => 0
  comm' := sorry

/-- The degree-zero component of the canonical chain map is the adjunct of
`onVars`. -/
theorem chainMap_f_zero (I1 : Ideal A1) (I2 : Ideal A2) {c : ℕ} (hc : 1 ≤ c)
    (hI : I1.map (algebraMap A1 A2) ^ c ≤ I2) (hI2 : I2.FG)
    [Algebra.TopologicallyFiniteType I1 B1] [Fintype ι]
    (P : Presentation A1 B1 I1 ι) :
    (chainMap I1 I2 hc hI hI2 P).f 0 = chainMapZero I1 I2 P := sorry

/-- The degree-one component of the canonical chain map is the adjunct of
`Cotangent.map toBaseChangeHom`. -/
theorem chainMap_f_one (I1 : Ideal A1) (I2 : Ideal A2) {c : ℕ} (hc : 1 ≤ c)
    (hI : I1.map (algebraMap A1 A2) ^ c ≤ I2) (hI2 : I2.FG)
    [Algebra.TopologicallyFiniteType I1 B1] [Fintype ι]
    (P : Presentation A1 B1 I1 ι) :
    (chainMap I1 I2 hc hI hI2 P).f 1 = chainMapOne I1 I2 hc hI hI2 P := sorry

/-- The induced map on `H^0`, i.e. homology in degree `0`. -/
def homologyZero (I1 : Ideal A1) (I2 : Ideal A2) {c : ℕ} (hc : 1 ≤ c)
    (hI : I1.map (algebraMap A1 A2) ^ c ≤ I2) (hI2 : I2.FG)
    [Algebra.TopologicallyFiniteType I1 B1] [Fintype ι]
    (P : Presentation A1 B1 I1 ι) :
    (scalarExtension I1 I2 P).homology 0 ⟶
      (naiveCotangent I2 (Presentation.baseChange I1 I2 hc hI hI2 P)).homology 0 :=
  HomologicalComplex.homologyMap (chainMap I1 I2 hc hI hI2 P) 0

/-- The induced map on `H^{-1}`, i.e. homology in degree `1`. -/
def homologyOne (I1 : Ideal A1) (I2 : Ideal A2) {c : ℕ} (hc : 1 ≤ c)
    (hI : I1.map (algebraMap A1 A2) ^ c ≤ I2) (hI2 : I2.FG)
    [Algebra.TopologicallyFiniteType I1 B1] [Fintype ι]
    (P : Presentation A1 B1 I1 ι) :
    (scalarExtension I1 I2 P).homology 1 ⟶
      (naiveCotangent I2 (Presentation.baseChange I1 I2 hc hI hI2 P)).homology 1 :=
  HomologicalComplex.homologyMap (chainMap I1 I2 hc hI hI2 P) 1

/-- `homologyZero` is the homology map of `chainMap` in degree `0`. -/
theorem homologyZero_eq (I1 : Ideal A1) (I2 : Ideal A2) {c : ℕ} (hc : 1 ≤ c)
    (hI : I1.map (algebraMap A1 A2) ^ c ≤ I2) (hI2 : I2.FG)
    [Algebra.TopologicallyFiniteType I1 B1] [Fintype ι]
    (P : Presentation A1 B1 I1 ι) :
    homologyZero I1 I2 hc hI hI2 P =
      HomologicalComplex.homologyMap (chainMap I1 I2 hc hI hI2 P) 0 := sorry

/-- `homologyOne` is the homology map of `chainMap` in degree `1`. -/
theorem homologyOne_eq (I1 : Ideal A1) (I2 : Ideal A2) {c : ℕ} (hc : 1 ≤ c)
    (hI : I1.map (algebraMap A1 A2) ^ c ≤ I2) (hI2 : I2.FG)
    [Algebra.TopologicallyFiniteType I1 B1] [Fintype ι]
    (P : Presentation A1 B1 I1 ι) :
    homologyOne I1 I2 hc hI hI2 P =
      HomologicalComplex.homologyMap (chainMap I1 I2 hc hI hI2 P) 1 := sorry

/-- The degree-one component of the canonical chain map,
`J1 / J1² ⊗_{B1} B2 → J2 / J2²`, is surjective, since `J2` is generated by
the image of `J1`. -/
theorem cotangentMap_surjective (I1 : Ideal A1) (I2 : Ideal A2) {c : ℕ} (hc : 1 ≤ c)
    (hI : I1.map (algebraMap A1 A2) ^ c ≤ I2) (hI2 : I2.FG)
    [Algebra.TopologicallyFiniteType I1 B1] [Fintype ι]
    (P : Presentation A1 B1 I1 ι) :
    Function.Surjective (chainMapOne I1 I2 hc hI hI2 P).hom := sorry

/-- The completed base-change comparison is independent of a finite presentation
    up to homotopy equivalences forming a homotopy-commutative square. -/
theorem chainMap_presentation_independent (I1 : Ideal A1) (I2 : Ideal A2) {c : ℕ}
    (hc : 1 ≤ c) (hI : I1.map (algebraMap A1 A2) ^ c ≤ I2) (hI2 : I2.FG)
    [Algebra.TopologicallyFiniteType I1 B1] [Fintype ι]
    {ι' : Type u} [Fintype ι']
    (P : Presentation A1 B1 I1 ι) (Q : Presentation A1 B1 I1 ι') :
    ∃ (e1 : HomotopyEquiv (scalarExtension I1 I2 P) (scalarExtension I1 I2 Q))
      (e2 : HomotopyEquiv
        (naiveCotangent I2 (Presentation.baseChange I1 I2 hc hI hI2 P))
        (naiveCotangent I2 (Presentation.baseChange I1 I2 hc hI hI2 Q))),
      Nonempty (Homotopy (e1.hom ≫ chainMap I1 I2 hc hI hI2 Q)
        (chainMap I1 I2 hc hI hI2 P ≫ e2.hom)) := sorry

end BaseChange

/-- The completed base-change comparison of finite completed polynomial
    presentations over Noetherian bases induces a bijection on degree-zero homology. -/
theorem homologyZero_bijective
    {A1 A2 B1 ι : Type u}
    [CommRing A1] [CommRing A2] [Algebra A1 A2] [CommRing B1] [Algebra A1 B1]
    [IsNoetherianRing A1] [IsNoetherianRing A2]
    (I1 : Ideal A1) (I2 : Ideal A2) {c : ℕ} (hc : 1 ≤ c)
    (hI : I1.map (algebraMap A1 A2) ^ c ≤ I2) (hI2 : I2.FG)
    [Algebra.TopologicallyFiniteType I1 B1] [Fintype ι]
    (P : Presentation A1 B1 I1 ι) :
    Function.Bijective (BaseChange.homologyZero I1 I2 hc hI hI2 P) := sorry

/-- The completed base-change comparison of finite completed polynomial
    presentations over Noetherian bases induces a surjection on degree-one homology. -/
theorem homologyOne_surjective
    {A1 A2 B1 ι : Type u}
    [CommRing A1] [CommRing A2] [Algebra A1 A2] [CommRing B1] [Algebra A1 B1]
    [IsNoetherianRing A1] [IsNoetherianRing A2]
    (I1 : Ideal A1) (I2 : Ideal A2) {c : ℕ} (hc : 1 ≤ c)
    (hI : I1.map (algebraMap A1 A2) ^ c ≤ I2) (hI2 : I2.FG)
    [Algebra.TopologicallyFiniteType I1 B1] [Fintype ι]
    (P : Presentation A1 B1 I1 ι) :
    Function.Surjective (BaseChange.homologyOne I1 I2 hc hI hI2 P) := sorry

end Algebra.NaiveCotangent.Adic
