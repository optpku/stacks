/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.DifferentialGraded.Algebra.Monoid
public import ReasLib.CategoryTheory.Functor.Equivalence
import Mathlib.Tactic.CrossRefAttribute

/-!
# Differential graded algebras as monoid objects

Differential graded algebras over a commutative ring sheaf are equivalent to monoid objects in the
monoidal category of cochain complexes of modules.  The inverse construction extracts the unit and
every homogeneous multiplication map from the corresponding morphisms of total complexes.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory ComplexShape
open scoped SheafOfModules.RingedSite.DifferentialGradedAlgebra

noncomputable section

universe u v w

namespace SheafOfModules.RingedSite.DifferentialGradedAlgebra

section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable [HasWeakSheafify J AddCommGrpCat.{w}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [UnivLE.{max u v, w}]
variable {𝒪 : Sheaf J CommRingCat.{w}}

-- Local declaration justification (parser conflict): these aliases only abbreviate the canonical
-- ambient module and cochain-complex categories; they install no data, instance, or public syntax.
local notation "ModO" => moduleCategory (J := J) (𝒪 := 𝒪)
local notation "CpxO" => CochainComplex ModO ℤ

/-- The degree-zero unit extracted from a monoid object in cochain complexes. -/
@[stacks 0FRF "monoid-object unit component"]
noncomputable def ofMonOne (A : Mon CpxO) : 𝟙_ ModO ⟶ A.X.X 0 :=
  HomologicalComplex.Monoidal.unitHomComponent A.mon.one

/-- The homogeneous multiplication extracted from a monoid object in cochain complexes. -/
@[stacks 0FRF "monoid-object multiplication component"]
noncomputable def ofMonMul (A : Mon CpxO) (n m : ℤ) :
    MonoidalCategoryStruct.tensorObj (C := ModO) (A.X.X n) (A.X.X m) ⟶
      A.X.X (n + m) :=
  HomologicalComplex.Monoidal.tensorHomComponent A.mon.mul n m

private theorem ofMonMul_component_comp (A : Mon CpxO) (n m k : ℤ) (h : n + m = k) :
    ofMonMul A n m ≫ eqToHom (congrArg A.X.X h) =
      HomologicalComplex.ιTensorObj A.X A.X n m k h ≫ A.mon.mul.f k := by
  subst k
  simp only [eqToHom_refl, Category.comp_id]
  rfl

/-- The extracted homogeneous multiplication is associative. -/
theorem ofMon_mul_assoc (A : Mon CpxO) :
    ∀ n m k : ℤ,
      (α_ (A.X.X n) (A.X.X m) (A.X.X k)).hom ≫
          (A.X.X n ◁ ofMonMul A m k) ≫ ofMonMul A n (m + k) =
        (ofMonMul A n m ▷ A.X.X k) ≫ ofMonMul A (n + m) k ≫
          eqToHom (congrArg A.X.X (Int.add_assoc n m k)) := by
  intro n m k
  rw [ofMonMul_component_comp A (n + m) k (n + (m + k)) (Int.add_assoc n m k)]
  let j : ℤ := n + (m + k)
  let lι := (HomologicalComplex.ιTensorObj A.X A.X n m (n + m) rfl ▷ A.X.X k) ≫
    HomologicalComplex.ιTensorObj (HomologicalComplex.tensorObj A.X A.X) A.X
      (n + m) k j (Int.add_assoc n m k)
  let rι := (A.X.X n ◁ HomologicalComplex.ιTensorObj A.X A.X m k (m + k) rfl) ≫
    HomologicalComplex.ιTensorObj A.X (HomologicalComplex.tensorObj A.X A.X)
      n (m + k) j rfl
  have hα : lι ≫ (α_ A.X A.X A.X).hom.f j =
      (α_ (A.X.X n) (A.X.X m) (A.X.X k)).hom ≫ rι := by
    exact CategoryTheory.GradedObject.Monoidal.ιTensorObj₃'_associator_hom
      A.X.X A.X.X A.X.X n m k j (Int.add_assoc n m k)
  have h := congrArg
    (fun g : (A.X ⊗ A.X) ⊗ A.X ⟶ A.X ↦ lι ≫ g.f j)
    (MonObj.mul_assoc A.X)
  change lι ≫ ((HomologicalComplex.tensorHom A.mon.mul (𝟙 A.X)).f j ≫
      A.mon.mul.f j) =
    lι ≫ ((α_ A.X A.X A.X).hom.f j ≫
      (HomologicalComplex.tensorHom (𝟙 A.X) A.mon.mul).f j ≫ A.mon.mul.f j) at h
  have hα' := congrArg
    (fun g ↦ g ≫ (HomologicalComplex.tensorHom (𝟙 A.X) A.mon.mul).f j ≫ A.mon.mul.f j) hα
  simp only [Category.assoc] at hα'
  rw [hα'] at h
  have hL := HomologicalComplex.ι_mapBifunctorMap
    (F := curriedTensor ModO) (c := up ℤ) A.mon.mul (𝟙 A.X)
      (n + m) k j (Int.add_assoc n m k)
  change HomologicalComplex.ιTensorObj (HomologicalComplex.tensorObj A.X A.X) A.X
      (n + m) k j (Int.add_assoc n m k) ≫
        (HomologicalComplex.tensorHom A.mon.mul (𝟙 A.X)).f j =
      (A.mon.mul.f (n + m) ▷ A.X.X k) ≫
        (A.X.X (n + m) ◁ (𝟙 A.X : A.X ⟶ A.X).f k) ≫
          HomologicalComplex.ιTensorObj A.X A.X (n + m) k j (Int.add_assoc n m k) at hL
  have hR := HomologicalComplex.ι_mapBifunctorMap
    (F := curriedTensor ModO) (c := up ℤ) (𝟙 A.X) A.mon.mul n (m + k) j rfl
  change HomologicalComplex.ιTensorObj A.X (HomologicalComplex.tensorObj A.X A.X)
      n (m + k) j rfl ≫
        (HomologicalComplex.tensorHom (𝟙 A.X) A.mon.mul).f j =
      ((𝟙 A.X : A.X ⟶ A.X).f n ▷
        (HomologicalComplex.tensorObj A.X A.X).X (m + k)) ≫
        (A.X.X n ◁ A.mon.mul.f (m + k)) ≫
          HomologicalComplex.ιTensorObj A.X A.X n (m + k) j rfl at hR
  have hL' := congrArg (fun g ↦ g ≫ A.mon.mul.f j) hL
  have hR' := congrArg (fun g ↦ g ≫ A.mon.mul.f j) hR
  simp only [HomologicalComplex.id_f, whiskerLeft_id, Category.id_comp,
    Category.assoc] at hL'
  simp only [HomologicalComplex.id_f, id_whiskerRight, Category.id_comp,
    Category.assoc] at hR'
  dsimp only [lι, rι] at h
  simp only [Category.assoc] at h
  rw [hL', hR'] at h
  simpa only [j, ofMonMul, HomologicalComplex.Monoidal.tensorHomComponent,
    comp_whiskerRight, MonoidalCategory.whiskerLeft_comp, Category.assoc] using h.symm

/-- The extracted degree-zero unit acts as a left identity. -/
theorem ofMon_one_mul (A : Mon CpxO) :
    ∀ n : ℤ,
      (λ_ (A.X.X n)).hom =
        (ofMonOne A ▷ A.X.X n) ≫ ofMonMul A 0 n ≫
          eqToHom (congrArg A.X.X (zero_add n)) := by
  intro n
  rw [ofMonMul_component_comp A 0 n n (zero_add n)]
  have h := congrArg (fun g : A.X ⟶ A.X ↦ g.f n)
    (show (λ_ A.X).inv ≫ (A.mon.one ▷ A.X) ≫ A.mon.mul = 𝟙 A.X by simp)
  change (HomologicalComplex.leftUnitor' A.X).inv n ≫
      (HomologicalComplex.tensorHom A.mon.one (𝟙 A.X)).f n ≫ A.mon.mul.f n =
        𝟙 (A.X.X n) at h
  have hL := HomologicalComplex.leftUnitor'_inv A.X n
  have hT := HomologicalComplex.ι_mapBifunctorMap
    (F := curriedTensor ModO) (c := up ℤ) A.mon.one (𝟙 A.X) 0 n n (zero_add n)
  change HomologicalComplex.ιTensorObj (HomologicalComplex.tensorUnit ModO (up ℤ)) A.X
      0 n n (zero_add n) ≫
        (HomologicalComplex.tensorHom A.mon.one (𝟙 A.X)).f n =
    (A.mon.one.f 0 ▷ A.X.X n) ≫ (A.X.X 0 ◁ (𝟙 A.X : A.X ⟶ A.X).f n) ≫
      HomologicalComplex.ιTensorObj A.X A.X 0 n n (zero_add n) at hT
  rw [hL] at h
  simp only [Category.assoc] at h
  have hT' := congrArg (fun g ↦ g ≫ A.mon.mul.f n) hT
  simp only [Category.assoc] at hT'
  rw [hT'] at h
  simp only [HomologicalComplex.id_f, whiskerLeft_id, Category.id_comp] at h
  apply (cancel_epi (λ_ (A.X.X n)).inv).mp
  simpa only [ofMonOne, HomologicalComplex.Monoidal.unitHomComponent,
    comp_whiskerRight, Category.assoc, Iso.inv_hom_id] using h.symm

/-- The extracted degree-zero unit acts as a right identity. -/
theorem ofMon_mul_one (A : Mon CpxO) :
    ∀ n : ℤ,
      (ρ_ (A.X.X n)).hom =
        (A.X.X n ◁ ofMonOne A) ≫ ofMonMul A n 0 ≫
          eqToHom (congrArg A.X.X (add_zero n)) := by
  intro n
  rw [ofMonMul_component_comp A n 0 n (add_zero n)]
  have h := congrArg (fun g : A.X ⟶ A.X ↦ g.f n)
    (show (ρ_ A.X).inv ≫ (A.X ◁ A.mon.one) ≫ A.mon.mul = 𝟙 A.X by simp)
  change (HomologicalComplex.rightUnitor' A.X).inv n ≫
      (HomologicalComplex.tensorHom (𝟙 A.X) A.mon.one).f n ≫ A.mon.mul.f n =
        𝟙 (A.X.X n) at h
  have hR := HomologicalComplex.rightUnitor'_inv A.X n
  have hT := HomologicalComplex.ι_mapBifunctorMap
    (F := curriedTensor ModO) (c := up ℤ) (𝟙 A.X) A.mon.one n 0 n (add_zero n)
  change HomologicalComplex.ιTensorObj A.X (HomologicalComplex.tensorUnit ModO (up ℤ))
      n 0 n (add_zero n) ≫
        (HomologicalComplex.tensorHom (𝟙 A.X) A.mon.one).f n =
    ((𝟙 A.X : A.X ⟶ A.X).f n ▷
      (HomologicalComplex.tensorUnit ModO (up ℤ)).X 0) ≫ (A.X.X n ◁ A.mon.one.f 0) ≫
      HomologicalComplex.ιTensorObj A.X A.X n 0 n (add_zero n) at hT
  rw [hR] at h
  simp only [Category.assoc] at h
  have hT' := congrArg (fun g ↦ g ≫ A.mon.mul.f n) hT
  simp only [Category.assoc] at hT'
  rw [hT'] at h
  simp only [HomologicalComplex.id_f, id_whiskerRight, Category.id_comp] at h
  apply (cancel_epi (ρ_ (A.X.X n)).inv).mp
  simpa only [ofMonOne, HomologicalComplex.Monoidal.unitHomComponent,
    MonoidalCategory.whiskerLeft_comp, Category.assoc, Iso.inv_hom_id] using h.symm

/-- The extracted homogeneous multiplication satisfies the graded Leibniz rule. -/
theorem ofMon_d_mul (A : Mon CpxO) :
    ∀ n m : ℤ,
      ofMonMul A n m ≫ A.X.d (n + m) (n + m + 1) =
        ((A.X.d n (n + 1)) ▷ A.X.X m) ≫ ofMonMul A (n + 1) m ≫
          eqToHom
            (congrArg A.X.X
              ((Int.add_assoc n 1 m).trans
                ((congrArg (fun p : ℤ ↦ n + p) (Int.add_comm 1 m)).trans
                  (Int.add_assoc n m 1).symm))) +
        n.negOnePow •
          ((A.X.X n ◁ A.X.d m (m + 1)) ≫ ofMonMul A n (m + 1) ≫
            eqToHom (congrArg A.X.X (Int.add_assoc n m 1).symm)) := by
  intro n m
  rw [ofMonMul_component_comp A (n + 1) m (n + m + 1)
    (add_right_comm n 1 m), ofMonMul_component_comp A n (m + 1) (n + m + 1) (add_assoc n m 1).symm]
  have hd : HomologicalComplex.ιTensorObj A.X A.X n m (n + m) rfl ≫
      (HomologicalComplex.tensorObj A.X A.X).d (n + m) (n + m + 1) =
    (A.X.d n (n + 1) ▷ A.X.X m) ≫
        HomologicalComplex.ιTensorObj A.X A.X (n + 1) m (n + m + 1)
          (add_right_comm n 1 m) +
      n.negOnePow • ((A.X.X n ◁ A.X.d m (m + 1)) ≫
        HomologicalComplex.ιTensorObj A.X A.X n (m + 1) (n + m + 1)
          (add_assoc n m 1).symm) := by
    change HomologicalComplex.ιMapBifunctor A.X A.X (curriedTensor ModO) (up ℤ)
      n m (n + m) rfl ≫
      (HomologicalComplex.mapBifunctor A.X A.X (curriedTensor ModO) (up ℤ)).d
        (n + m) (n + m + 1) = _
    rw [HomologicalComplex.mapBifunctor.d_eq, Preadditive.comp_add,
      HomologicalComplex.mapBifunctor.ι_D₁, HomologicalComplex.mapBifunctor.ι_D₂,
      HomologicalComplex.mapBifunctor.d₁_eq A.X A.X (curriedTensor ModO) (up ℤ)
        (show (up ℤ).Rel n (n + 1) from rfl) m (n + m + 1) (add_right_comm n 1 m),
      HomologicalComplex.mapBifunctor.d₂_eq A.X A.X (curriedTensor ModO) (up ℤ)
        n (show (up ℤ).Rel m (m + 1) from rfl) (n + m + 1) (add_assoc n m 1).symm]
    change (1 : ℤˣ) • _ + n.negOnePow • _ = _
    simp only [one_smul]
    rfl
  have hc := (A.mon.mul.comm (n + m) (n + m + 1)).symm
  change (HomologicalComplex.tensorObj A.X A.X).d (n + m) (n + m + 1) ≫
      A.mon.mul.f (n + m + 1) =
    A.mon.mul.f (n + m) ≫ A.X.d (n + m) (n + m + 1) at hc
  have h := congrArg
    (fun g ↦ HomologicalComplex.ιTensorObj A.X A.X n m (n + m) rfl ≫ g) hc
  have hd' := congrArg (fun g ↦ g ≫ A.mon.mul.f (n + m + 1)) hd
  have hh := (Category.assoc
    (HomologicalComplex.ιTensorObj A.X A.X n m (n + m) rfl)
    ((HomologicalComplex.tensorObj A.X A.X).d (n + m) (n + m + 1))
    (A.mon.mul.f (n + m + 1))).trans h
  simpa only [ofMonMul, HomologicalComplex.Monoidal.tensorHomComponent,
    Category.assoc, Preadditive.add_comp, Linear.units_smul_comp] using hh.symm.trans hd'

/-- Recover a differential graded algebra from a monoid object in cochain complexes. -/
@[stacks 0FRF "inverse monoid-object bridge"]
noncomputable def ofMon (A : Mon CpxO) : DGA(𝒪) where
  toComplex := A.X
  mul := ofMonMul A
  one := ofMonOne A
  mul_assoc := ofMon_mul_assoc A
  one_mul := ofMon_one_mul A
  mul_one := ofMon_mul_one A
  d_mul := ofMon_d_mul A

/-- A monoid morphism preserves the extracted degree-zero units. -/
theorem ofMonMap_comm_one {A B : Mon CpxO} (f : A ⟶ B) :
    ofMonOne A ≫ f.hom.f 0 = ofMonOne B := by
  have h := congrArg
    (fun g : 𝟙_ CpxO ⟶ B.X ↦ HomologicalComplex.Monoidal.unitHomComponent g)
    (IsMonHom.one_hom f.hom)
  simpa only [ofMonOne, HomologicalComplex.Monoidal.unitHomComponent,
    HomologicalComplex.comp_f, Category.assoc] using h

/-- A monoid morphism preserves every extracted homogeneous multiplication. -/
theorem ofMonMap_comm_mul {A B : Mon CpxO} (f : A ⟶ B) :
    ∀ n m : ℤ,
      ofMonMul A n m ≫ f.hom.f (n + m) =
        ((f.hom.f n) ▷ A.X.X m) ≫ (B.X.X n ◁ f.hom.f m) ≫ ofMonMul B n m := by
  intro n m
  have h := congrArg (fun g : A.X ⊗ A.X ⟶ B.X ↦ g.f (n + m))
    (IsMonHom.mul_hom f.hom)
  change A.mon.mul.f (n + m) ≫ f.hom.f (n + m) =
    (HomologicalComplex.tensorHom f.hom f.hom).f (n + m) ≫ B.mon.mul.f (n + m) at h
  have hι := HomologicalComplex.ι_mapBifunctorMap
    (F := curriedTensor ModO) (c := up ℤ) f.hom f.hom n m (n + m) rfl
  change HomologicalComplex.ιTensorObj A.X A.X n m (n + m) rfl ≫
      (HomologicalComplex.tensorHom f.hom f.hom).f (n + m) =
    (f.hom.f n ▷ A.X.X m) ≫ (B.X.X n ◁ f.hom.f m) ≫
      HomologicalComplex.ιTensorObj B.X B.X n m (n + m) rfl at hι
  have h' := congrArg
    (fun g ↦ HomologicalComplex.ιTensorObj A.X A.X n m (n + m) rfl ≫ g) h
  have hι' := congrArg (fun g ↦ g ≫ B.mon.mul.f (n + m)) hι
  have hh : HomologicalComplex.ιTensorObj A.X A.X n m (n + m) rfl ≫
      (A.mon.mul.f (n + m) ≫ f.hom.f (n + m)) =
      (HomologicalComplex.ιTensorObj A.X A.X n m (n + m) rfl ≫
        (HomologicalComplex.tensorHom f.hom f.hom).f (n + m)) ≫ B.mon.mul.f (n + m) :=
    h'.trans (Category.assoc _ _ _).symm
  simpa only [ofMonMul, HomologicalComplex.Monoidal.tensorHomComponent,
    Category.assoc] using hh.trans hι'

/-- A monoid morphism as a morphism between the recovered differential graded algebras. -/
noncomputable def ofMonMap {A B : Mon CpxO} (f : A ⟶ B) : ofMon A ⟶ ofMon B where
  hom := f.hom
  comm_one := ofMonMap_comm_one f
  comm_mul := ofMonMap_comm_mul f

/-- Recovering differential graded algebra maps preserves identity morphisms. -/
theorem ofMonMap_id (A : Mon CpxO) :
    ofMonMap (𝟙 A) = 𝟙 (ofMon A) := by
  apply Hom.ext
  rfl

/-- Recovering differential graded algebra maps preserves composition. -/
theorem ofMonMap_comp {A B D : Mon CpxO} (f : A ⟶ B) (g : B ⟶ D) :
    ofMonMap (f ≫ g) = ofMonMap f ≫ ofMonMap g := by
  apply Hom.ext
  rfl

/-- The inverse functor from cochain-complex monoid objects to differential graded algebras. -/
@[stacks 0FRF "inverse monoid-object functor"]
noncomputable def ofMonFunctor : Mon CpxO ⥤ DGA(𝒪) where
  obj := ofMon
  map := ofMonMap
  map_id := ofMonMap_id
  map_comp := ofMonMap_comp

/-- The identity cochain map preserves the unit when comparing a differential graded algebra with
the object recovered from its associated monoid. -/
theorem toMonUnitHom_comm_one (A : DGA(𝒪)) :
    A.one ≫ (𝟙 A.toComplex : A.toComplex ⟶ A.toComplex).f 0 =
      (ofMon A.toMon).one := by
  have h : HomologicalComplex.Monoidal.unitHomComponent (oneHom A) = A.one := by
    dsimp only [HomologicalComplex.Monoidal.unitHomComponent, oneHom]
    simp [HomologicalComplex.tensorUnitIso,
      CategoryTheory.GradedObject.Monoidal.oneHom, HomologicalComplex.singleObjXSelf,
      Category.assoc]
  change A.one ≫ 𝟙 (A.toComplex.X 0) =
    HomologicalComplex.Monoidal.unitHomComponent (oneHom A)
  exact (Category.comp_id A.one).trans h.symm

/-- The identity cochain map preserves multiplication when comparing a differential graded algebra
with the object recovered from its associated monoid. -/
theorem toMonUnitHom_comm_mul (A : DGA(𝒪)) :
    ∀ n m : ℤ,
      A.mul n m ≫ (𝟙 A.toComplex : A.toComplex ⟶ A.toComplex).f (n + m) =
        (((𝟙 A.toComplex : A.toComplex ⟶ A.toComplex).f n) ▷ A.toComplex.X m) ≫
          ((ofMon A.toMon).toComplex.X n ◁
            (𝟙 A.toComplex : A.toComplex ⟶ A.toComplex).f m) ≫
            (ofMon A.toMon).mul n m := by
  intro n m
  have h : HomologicalComplex.Monoidal.tensorHomComponent (mulHom A) n m =
      A.mul n m := by
    exact (HomologicalComplex.ι_mapBifunctorDesc
      (K₁ := A.toComplex) (K₂ := A.toComplex)
      (F := curriedTensor (ringedSiteModuleCategory J 𝒪)) (c := up ℤ) (j := n + m)
      (fun p q h ↦ A.mul p q ≫ eqToHom (congrArg A.toComplex.X h)) n m rfl).trans
        (Category.comp_id (A.mul n m))
  change A.mul n m ≫ 𝟙 (A.toComplex.X (n + m)) =
    ((𝟙 (A.toComplex.X n)) ▷ A.toComplex.X m) ≫
      (A.toComplex.X n ◁ 𝟙 (A.toComplex.X m)) ≫
        HomologicalComplex.Monoidal.tensorHomComponent (mulHom A) n m
  simpa only [id_whiskerRight, whiskerLeft_id, Category.id_comp, Category.comp_id] using
    h.symm

/-- The forward identity-carrier comparison with the recovered differential graded algebra. -/
noncomputable def toMonUnitHom (A : DGA(𝒪)) : A ⟶ ofMon A.toMon where
  hom := 𝟙 A.toComplex
  comm_one := toMonUnitHom_comm_one A
  comm_mul := toMonUnitHom_comm_mul A

/-- The reverse identity cochain map preserves the unit in the monoid-recovery comparison. -/
theorem toMonUnitInv_comm_one (A : DGA(𝒪)) :
    (ofMon A.toMon).one ≫ (𝟙 A.toComplex : A.toComplex ⟶ A.toComplex).f 0 =
      A.one := by
  have h : A.one = (ofMon A.toMon).one :=
    (Category.comp_id A.one).symm.trans (toMonUnitHom_comm_one A)
  change (ofMon A.toMon).one ≫ 𝟙 (A.toComplex.X 0) = A.one
  exact (Category.comp_id ((ofMon A.toMon).one)).trans h.symm

/-- The reverse identity cochain map preserves multiplication in the monoid-recovery comparison. -/
theorem toMonUnitInv_comm_mul (A : DGA(𝒪)) :
    ∀ n m : ℤ,
      (ofMon A.toMon).mul n m ≫
          (𝟙 A.toComplex : A.toComplex ⟶ A.toComplex).f (n + m) =
        (((𝟙 A.toComplex : A.toComplex ⟶ A.toComplex).f n) ▷
            (ofMon A.toMon).toComplex.X m) ≫
          (A.toComplex.X n ◁
            (𝟙 A.toComplex : A.toComplex ⟶ A.toComplex).f m) ≫ A.mul n m := by
  intro n m
  have h := toMonUnitHom_comm_mul A n m
  change A.mul n m ≫ 𝟙 (A.toComplex.X (n + m)) =
    ((𝟙 (A.toComplex.X n)) ▷ A.toComplex.X m) ≫
      (A.toComplex.X n ◁ 𝟙 (A.toComplex.X m)) ≫
        HomologicalComplex.Monoidal.tensorHomComponent (mulHom A) n m at h
  have hm : A.mul n m =
      HomologicalComplex.Monoidal.tensorHomComponent (mulHom A) n m := by
    simpa only [id_whiskerRight, whiskerLeft_id, Category.id_comp, Category.comp_id] using h
  change HomologicalComplex.Monoidal.tensorHomComponent (mulHom A) n m ≫
      𝟙 (A.toComplex.X (n + m)) =
    ((𝟙 (A.toComplex.X n)) ▷ A.toComplex.X m) ≫
      (A.toComplex.X n ◁ 𝟙 (A.toComplex.X m)) ≫ A.mul n m
  simpa only [id_whiskerRight, whiskerLeft_id, Category.id_comp, Category.comp_id] using
    hm.symm

/-- The inverse identity-carrier comparison with the recovered differential graded algebra. -/
noncomputable def toMonUnitInv (A : DGA(𝒪)) : ofMon A.toMon ⟶ A where
  hom := 𝟙 A.toComplex
  comm_one := toMonUnitInv_comm_one A
  comm_mul := toMonUnitInv_comm_mul A

/-- The two identity-carrier comparisons compose to the identity on the original algebra. -/
theorem toMonUnitHom_inv (A : DGA(𝒪)) :
    toMonUnitHom A ≫ toMonUnitInv A = 𝟙 A := by
  apply Hom.ext
  change (𝟙 A.toComplex) ≫ 𝟙 A.toComplex = 𝟙 A.toComplex
  simp

/-- The two identity-carrier comparisons compose to the identity on the recovered algebra. -/
theorem toMonUnitInv_hom (A : DGA(𝒪)) :
    toMonUnitInv A ≫ toMonUnitHom A = 𝟙 (ofMon A.toMon) := by
  apply Hom.ext
  change (𝟙 A.toComplex) ≫ 𝟙 A.toComplex = 𝟙 A.toComplex
  simp

/-- A differential graded algebra is canonically isomorphic to the object recovered from its
associated monoid. -/
noncomputable def toMonUnitIso (A : DGA(𝒪)) : A ≅ ofMon A.toMon where
  hom := toMonUnitHom A
  inv := toMonUnitInv A
  hom_inv_id := toMonUnitHom_inv A
  inv_hom_id := toMonUnitInv_hom A

/-- The identity carrier map preserves the unit in the comparison from a recovered monoid. -/
theorem toMonCounit_one (A : Mon CpxO) :
    (ofMon A).toMon.mon.one ≫ (Iso.refl A.X).hom = A.mon.one := by
  apply HomologicalComplex.from_single_hom_ext
  change (oneHom (ofMon A)).f 0 ≫ 𝟙 (A.X.X 0) = A.mon.one.f 0
  change ((HomologicalComplex.tensorUnitIso ModO (up ℤ)).inv 0 ≫
    CategoryTheory.GradedObject.Monoidal.oneHom A.X.X (ofMonOne A) 0) ≫
      𝟙 (A.X.X 0) = A.mon.one.f 0
  simp [HomologicalComplex.tensorUnitIso,
    CategoryTheory.GradedObject.Monoidal.oneHom, ofMonOne,
    HomologicalComplex.Monoidal.unitHomComponent, HomologicalComplex.singleObjXSelf,
    Category.assoc]

/-- The identity carrier map preserves multiplication in the comparison from a recovered monoid. -/
theorem toMonCounit_mul (A : Mon CpxO) :
    (ofMon A).toMon.mon.mul ≫ (Iso.refl A.X).hom =
      ((Iso.refl A.X).hom ⊗ₘ (Iso.refl A.X).hom) ≫ A.mon.mul := by
  have h : mulHom (ofMon A) = A.mon.mul := by
    apply HomologicalComplex.hom_ext
    intro k
    apply HomologicalComplex.mapBifunctor.hom_ext
    intro n m hnm
    change n + m = k at hnm
    exact (HomologicalComplex.ι_mapBifunctorDesc
      (K₁ := A.X) (K₂ := A.X) (F := curriedTensor ModO) (c := up ℤ) (j := k)
      (fun p q h ↦ ofMonMul A p q ≫ eqToHom (congrArg A.X.X h)) n m hnm).trans
        (ofMonMul_component_comp A n m k hnm)
  change mulHom (ofMon A) ≫ 𝟙 A.X = ((𝟙 A.X) ⊗ₘ 𝟙 A.X) ≫ A.mon.mul
  have h' : mulHom (ofMon A) ≫ 𝟙 A.X = A.mon.mul :=
    (Category.comp_id (mulHom (ofMon A))).trans h
  have h'' : ((𝟙 A.X) ⊗ₘ 𝟙 A.X) ≫ A.mon.mul = A.mon.mul := by
    simp only [id_tensorHom_id, Category.id_comp]
  exact h'.trans h''.symm

/-- Recovering a differential graded algebra from a monoid and returning to monoids is canonically
isomorphic to the original monoid object. -/
noncomputable def toMonCounitIso (A : Mon CpxO) : (ofMon A).toMon ≅ A :=
  Mon.mkIso (Iso.refl A.X) (toMonCounit_one A) (toMonCounit_mul A)

/-- The algebra-side comparison is natural in differential graded algebra maps. -/
theorem toMonUnitIso_naturality {A B : DGA(𝒪)} (f : A ⟶ B) :
    f ≫ (toMonUnitIso B).hom =
      (toMonUnitIso A).hom ≫ (toMonFunctor ⋙ ofMonFunctor).map f := by
  apply Hom.ext
  change f.hom ≫ 𝟙 B.toComplex = (𝟙 A.toComplex) ≫ f.hom
  simp only [Category.comp_id, Category.id_comp]

/-- The monoid-side comparison is natural in monoid morphisms. -/
theorem toMonCounitIso_naturality {A B : Mon CpxO} (f : A ⟶ B) :
    (ofMonFunctor ⋙ toMonFunctor).map f ≫ (toMonCounitIso B).hom =
      (toMonCounitIso A).hom ≫ f := by
  apply Mon.Hom.ext
  change f.hom ≫ 𝟙 B.X = (𝟙 A.X) ≫ f.hom
  simp only [Category.comp_id, Category.id_comp]

/-- The natural unit comparison between differential graded algebras and recovered monoids. -/
noncomputable def toMonUnitNatIso :
    𝟭 DGA(𝒪) ≅ toMonFunctor ⋙ ofMonFunctor :=
  NatIso.ofComponents toMonUnitIso toMonUnitIso_naturality

/-- The natural counit comparison between recovered differential graded algebras and monoids. -/
noncomputable def toMonCounitNatIso :
    ofMonFunctor ⋙ toMonFunctor ≅ 𝟭 (Mon CpxO) :=
  NatIso.ofComponents toMonCounitIso toMonCounitIso_naturality

/-- Explicit quasi-inverse data for the cochain-monoid presentation of differential graded
algebras. -/
noncomputable def toMonQuasiInverse : Functor.QuasiInverse (toMonFunctor (𝒪 := 𝒪)) where
  inverse := ofMonFunctor
  unitIso := toMonUnitNatIso
  counitIso := toMonCounitNatIso

/-- Differential graded algebras over `𝒪` are equivalent to monoid objects in cochain complexes of
`𝒪`-modules. -/
@[stacks 0FRF "differential graded algebra monoid equivalence"]
noncomputable def toMonEquivalence : DGA(𝒪) ≌ Mon CpxO :=
  toMonQuasiInverse.adjointifyUnit

/-- The forward functor of `toMonEquivalence` is the canonical monoid-object functor. -/
@[simp]
theorem toMonEquivalence_functor :
    (toMonEquivalence (𝒪 := 𝒪)).functor = toMonFunctor := by
  rfl

/-- The inverse functor of `toMonEquivalence` recovers homogeneous DGA data. -/
@[simp]
theorem toMonEquivalence_inverse :
    (toMonEquivalence (𝒪 := 𝒪)).inverse = ofMonFunctor := by
  rfl

/-- The canonical functor from differential graded algebras to cochain monoids is an equivalence. -/
instance toMonFunctor_isEquivalence :
    (toMonFunctor (𝒪 := 𝒪)).IsEquivalence := by
  exact (toMonQuasiInverse (𝒪 := 𝒪)).isEquivalence

end

end SheafOfModules.RingedSite.DifferentialGradedAlgebra

end
