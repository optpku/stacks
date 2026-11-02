/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicTopology.SimplicialObject.DoldKan.LowerFace
public import ReasLib.Algebra.Homology.HomologicalComplex.DifferentialRescale.Equivalence
public import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
public import Mathlib.CategoryTheory.Center.NegOnePow
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Signed lower-face normalized Moore complexes

The lower-face Dold--Kan functor has the right normalized subobjects but uses the raw last face as
its differential.  The source convention for the normalized complex multiplies the differential
out of degree `n` by `(-1)^n`.  This leaf owns that signed functor, its comparison with the raw
lower-face Dold--Kan owner, and the canonical inclusion into the alternating-face complex.
@stack 0194
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicTopology
open scoped Simplicial

noncomputable section

universe v u

namespace AlgebraicTopology

variable {A : Type u} [Category.{v} A]

namespace normalizedMooreComplex

namespace lowerFace

section Sign

variable [Preadditive A]

/-- The central unit `(-1)^n` used to rescale a differential out of degree `n`. -/
@[stacks 0194 "source-degree lower-face sign"]
noncomputable def sign (n : ℕ) : (CatCenter A)ˣ :=
  (-1 : (CatCenter A)ˣ) ^ n

/-- Acting by the central sign is the usual integer `(-1)^n` action on a morphism. -/
@[simp, stacks 0194 "source-degree lower-face sign action"]
theorem sign_smul (n : ℕ) {X Y : A} (f : X ⟶ Y) :
    HomologicalComplex.Rescale.Units.scalar (sign (A := A)) n • f =
      (n : ℤ).negOnePow • f := by
  rw [CatCenter.smul_eq]
  change f ≫ (((-1 : (CatCenter A)ˣ) ^ n).val.app Y) = _
  rw [← zpow_natCast, CatCenter.app_neg_one_zpow]
  simp

end Sign

section Differential

variable [Abelian A]

/-- The source-signed lower-face differential out of degree `m + 1`. -/
@[stacks 0194 "signed lower-face normalized Moore differential"]
noncomputable def d (U : SimplicialObject A) (m : ℕ) :
    (SimplicialObject.normalizedMoore.lowerFace.subobject U (m + 1) : A) ⟶
      (SimplicialObject.normalizedMoore.lowerFace.subobject U m : A) :=
  HomologicalComplex.Rescale.Units.scalar (sign (A := A)) (m + 1) •
    SimplicialObject.normalizedMoore.lowerFace.lastFace U m

end Differential

section Sign

variable [Preadditive A]

/-- The triangular central-unit potential comparing the signed and raw lower-face complexes. -/
@[stacks 0194 "lower-face sign potential"]
noncomputable def potential (n : ℕ) : (CatCenter A)ˣ :=
  (-1 : (CatCenter A)ˣ) ^ Nat.choose (n + 1) 2

/-- The triangular sign family is a potential for source-degree rescaling by `(-1)^n`. -/
@[stacks 0194 "lower-face sign potential recurrence"]
theorem potential_isPotential :
    HomologicalComplex.Rescale.IsPotential (c := ComplexShape.down ℕ)
      (sign (A := A)) (potential (A := A)) := by
  intro i j hij
  change j + 1 = i at hij
  subst i
  change (-1 : (CatCenter A)ˣ) ^ Nat.choose (j + 1 + 1) 2 =
    (-1 : (CatCenter A)ˣ) ^ (j + 1) * (-1 : (CatCenter A)ˣ) ^ Nat.choose (j + 1) 2
  rw [Nat.choose_succ_succ' (j + 1) 1, Nat.choose_one_right, pow_add]

/-- The source-degree rescaling functor used by the signed lower-face convention. -/
@[stacks 0194 "source-degree lower-face rescaling functor"]
noncomputable def rescaleFunctor : ChainComplex A ℕ ⥤ ChainComplex A ℕ :=
  HomologicalComplex.Rescale.Units.functor (C := A) (c := ComplexShape.down ℕ)
    (sign (A := A))

end Sign

end lowerFace

section Abelian

variable [Abelian A]

/-- The signed lower-face normalized Moore functor, defined by source-degree rescaling of the raw
lower-face Dold--Kan functor. -/
@[stacks 0194 "signed lower-face normalized Moore functor"]
noncomputable abbrev lowerFace : SimplicialObject A ⥤ ChainComplex A ℕ :=
  CategoryTheory.Abelian.DoldKan.N.lowerFace (A := A) ⋙
    lowerFace.rescaleFunctor (A := A)

/-- Source-facing notation for the lower-face normalized Moore complex, whose differential uses the
last face and the source-degree sign convention. -/
scoped[DoldKan] notation "Nₗ[" X "]" =>
  AlgebraicTopology.normalizedMooreComplex.lowerFace.obj X

namespace lowerFace

/-- The signed lower-face Dold--Kan equivalence, with inverse data inherited from the raw
lower-face equivalence and pointwise inverse sign rescaling. -/
@[stacks 0194 "signed lower-face Dold--Kan equivalence"]
noncomputable def equivalence :
    SimplicialObject A ≌ ChainComplex A ℕ :=
  (CategoryTheory.Abelian.DoldKan.N.lowerFace.equivalence (A := A)).trans
    (HomologicalComplex.Rescale.Units.equivalence
      (C := A) (c := ComplexShape.down ℕ) (sign (A := A)))

/-- The forward functor of the signed lower-face equivalence is the signed normalization
functor. -/
@[simp, stacks 0194 "signed lower-face equivalence forward functor"]
theorem equivalence.functor :
    (equivalence (A := A)).functor = lowerFace (A := A) := rfl

/-- The signed lower-face functor has the same graded objects as the raw lower-face owner. -/
@[simp, stacks 0194 "signed lower-face normalized Moore object formula"]
theorem obj_X (U : SimplicialObject A) (n : ℕ) :
    (lowerFace.obj U).X n =
      (SimplicialObject.normalizedMoore.lowerFace.subobject U n : A) := rfl

/-- The signed lower-face functor has the same graded maps as the raw lower-face owner. -/
@[simp, stacks 0194 "signed lower-face normalized Moore map formula"]
theorem map_f {U V : SimplicialObject A} (f : U ⟶ V) (n : ℕ) :
    (lowerFace.map f).f n =
      SimplicialObject.normalizedMoore.lowerFace.subobject.map f n := rfl

/-- The named source-signed differential is the differential of the rescaled lower-face functor. -/
@[stacks 0194 "signed lower-face normalized Moore named differential"]
theorem obj_d_eq (U : SimplicialObject A) (m : ℕ) :
    (lowerFace.obj U).d (m + 1) m = d U m := rfl

/-- The signed lower-face differential is `(-1)^n` times the restricted last face. -/
@[simp, stacks 0194 "signed lower-face normalized Moore differential formula"]
theorem obj_d (U : SimplicialObject A) (m : ℕ) :
    (lowerFace.obj U).d (m + 1) m =
      (m + 1 : ℤ).negOnePow •
        SimplicialObject.normalizedMoore.lowerFace.lastFace U m := by
  rw [obj_d_eq, d, sign_smul]
  simp only [Nat.cast_add, Nat.cast_one]

/-- The generic gauge comparison identifies the signed functor with the raw lower-face owner. -/
@[stacks 0194 "natural signed lower-face gauge comparison"]
noncomputable def rawNatIso :
    lowerFace ≅ CategoryTheory.Abelian.DoldKan.N.lowerFace (A := A) :=
  Functor.isoWhiskerLeft (CategoryTheory.Abelian.DoldKan.N.lowerFace (A := A))
      (HomologicalComplex.Rescale.natIso (C := A) (c := ComplexShape.down ℕ)
        (sign (A := A)) (potential (A := A)) (potential_isPotential (A := A))) ≪≫
    Functor.rightUnitor _

/-- The signed lower-face functor is naturally isomorphic to the raw lower-face Dold--Kan owner. -/
@[stacks 0194 "signed and raw lower-face normalized Moore comparison"]
noncomputable def rawIso (U : SimplicialObject A) :
    lowerFace.obj U ≅ CategoryTheory.Abelian.DoldKan.N.lowerFace.obj U :=
  (rawNatIso (A := A)).app U

/-- The forward components of `rawIso` are the canonical triangular sign gauges. -/
@[simp, stacks 0194 "signed-to-raw lower-face comparison component"]
theorem rawIso.hom_f (U : SimplicialObject A) (n : ℕ) :
    (rawIso U).hom.f n =
      (HomologicalComplex.Rescale.component
        (CategoryTheory.Abelian.DoldKan.N.lowerFace.obj U)
        (sign (A := A)) (potential (A := A)) n).hom := by
  simp [rawIso, rawNatIso, HomologicalComplex.Rescale.natIso,
    HomologicalComplex.Rescale.iso]
  exact Category.comp_id _

/-- The inverse components of `rawIso` are the inverse triangular sign gauges. -/
@[simp, stacks 0194 "raw-to-signed lower-face comparison component"]
theorem rawIso.inv_f (U : SimplicialObject A) (n : ℕ) :
    (rawIso U).inv.f n =
      (HomologicalComplex.Rescale.component
        (CategoryTheory.Abelian.DoldKan.N.lowerFace.obj U)
        (sign (A := A)) (potential (A := A)) n).inv := by
  simp [rawIso, rawNatIso, HomologicalComplex.Rescale.natIso,
    HomologicalComplex.Rescale.iso]
  exact Category.id_comp _

/-- The sign comparison is natural in the simplicial object. -/
@[reassoc, stacks 0194 "naturality of the signed lower-face comparison"]
theorem rawIso.hom_naturality {U V : SimplicialObject A} (f : U ⟶ V) :
    lowerFace.map f ≫ (rawIso V).hom =
      (rawIso U).hom ≫
        (CategoryTheory.Abelian.DoldKan.N.lowerFace (A := A)).map f := by
  exact (rawNatIso (A := A)).hom.naturality f

/-- The inverse signed-to-raw comparison is natural in the simplicial object. -/
@[reassoc, stacks 0194 "inverse naturality of the signed lower-face comparison"]
theorem rawIso.inv_naturality {U V : SimplicialObject A} (f : U ⟶ V) :
    (CategoryTheory.Abelian.DoldKan.N.lowerFace (A := A)).map f ≫ (rawIso V).inv =
      (rawIso U).inv ≫ lowerFace.map f := by
  exact (rawNatIso (A := A)).inv.naturality f

/-- The component of the signed-to-raw natural isomorphism is `rawIso`. -/
@[simp, stacks 0194 "signed-to-raw natural comparison component"]
theorem rawNatIso.app (U : SimplicialObject A) :
    (rawNatIso (A := A)).app U = rawIso U := rfl

/-- The forward signed-to-raw comparison is the triangular potential action in each degree. -/
@[simp, stacks 0194 "signed-to-raw lower-face scalar component"]
theorem rawIso.hom_f_action (U : SimplicialObject A) (n : ℕ) :
    (rawIso U).hom.f n =
      HomologicalComplex.Rescale.Units.scalar (potential (A := A)) n • 𝟙 _ := by
  rw [rawIso.hom_f]
  rfl

/-- The inverse raw-to-signed comparison is the inverse triangular potential action in each degree. -/
@[simp, stacks 0194 "raw-to-signed lower-face scalar component"]
theorem rawIso.inv_f_action (U : SimplicialObject A) (n : ℕ) :
    (rawIso U).inv.f n =
      HomologicalComplex.Rescale.Units.invScalar (potential (A := A)) n • 𝟙 _ := by
  rw [rawIso.inv_f]
  rfl

/-- The signed lower-face normalized Moore functor inherits equivalence from the raw owner and the
unit-family rescaling owner. -/
@[stacks 0194 "equivalence of signed lower-face normalized Moore functor"]
noncomputable instance isEquivalence : (lowerFace (A := A)).IsEquivalence :=
  (equivalence (A := A)).isEquivalence_functor

/-- The signed lower-face normalized Moore functor bundled as an exact functor. -/
@[stacks 0194 "exact signed lower-face normalized Moore functor",
  stacks 019B "exact source normalized Moore functor"]
noncomputable def exactFunctor :
    SimplicialObject A ⥤ₑ ChainComplex A ℕ :=
  ExactFunctor.of lowerFace

namespace inclusion

/-- The degreewise lower-face subobject arrows commute with all differentials of the alternating-face
complex. -/
@[reassoc, stacks 0198 "signed lower-face inclusion differential compatibility"]
theorem app_comm (U : SimplicialObject A) (i j : ℕ) :
    (SimplicialObject.normalizedMoore.lowerFace.subobject U i).arrow ≫
        ((alternatingFaceMapComplex A).obj U).d i j =
      (lowerFace.obj U).d i j ≫
        (SimplicialObject.normalizedMoore.lowerFace.subobject U j).arrow := sorry

/-- The chain map from signed lower-face normalization to the alternating-face complex at `U`. -/
@[stacks 0198 "signed lower-face inclusion map"]
noncomputable def app (U : SimplicialObject A) :
    lowerFace.obj U ⟶ (alternatingFaceMapComplex A).obj U where
  f n := (SimplicialObject.normalizedMoore.lowerFace.subobject U n).arrow
  comm' i j _ := app_comm U i j

/-- The source-signed normalized inclusion is natural in the simplicial object. -/
@[reassoc, stacks 0198 "naturality of the signed lower-face inclusion"]
theorem naturality {U V : SimplicialObject A} (f : U ⟶ V) :
    lowerFace.map f ≫ app V =
      app U ≫ (alternatingFaceMapComplex A).map f := by
  ext n
  exact SimplicialObject.normalizedMoore.lowerFace.subobject.map.arrow f n

/-- The signed lower-face normalized Moore inclusion into the alternating-face functor. -/
@[stacks 0198 "signed lower-face normalized Moore inclusion"]
noncomputable def natTrans :
    lowerFace ⟶ alternatingFaceMapComplex A where
  app := app
  naturality _ _ f := naturality f

/-- The component of the source-signed normalized inclusion natural transformation. -/
@[simp, stacks 0198 "signed lower-face inclusion natural component"]
theorem natTrans_app (U : SimplicialObject A) :
    (natTrans (A := A)).app U = app U := rfl

/-- The component of the signed lower-face inclusion is the normalized subobject arrow. -/
@[simp, stacks 0198 "signed lower-face inclusion component"]
theorem app_f (U : SimplicialObject A) (n : ℕ) :
    (app U).f n =
      (SimplicialObject.normalizedMoore.lowerFace.subobject U n).arrow := rfl

end inclusion

end lowerFace

end Abelian

end normalizedMooreComplex

end AlgebraicTopology
