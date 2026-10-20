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

/-- The extracted homogeneous multiplication is associative. -/
theorem ofMon_mul_assoc (A : Mon CpxO) :
    ∀ n m k : ℤ,
      (α_ (A.X.X n) (A.X.X m) (A.X.X k)).hom ≫
          (A.X.X n ◁ ofMonMul A m k) ≫ ofMonMul A n (m + k) =
        (ofMonMul A n m ▷ A.X.X k) ≫ ofMonMul A (n + m) k ≫
          eqToHom (congrArg A.X.X (Int.add_assoc n m k)) := sorry

/-- The extracted degree-zero unit acts as a left identity. -/
theorem ofMon_one_mul (A : Mon CpxO) :
    ∀ n : ℤ,
      (λ_ (A.X.X n)).hom =
        (ofMonOne A ▷ A.X.X n) ≫ ofMonMul A 0 n ≫
          eqToHom (congrArg A.X.X (zero_add n)) := sorry

/-- The extracted degree-zero unit acts as a right identity. -/
theorem ofMon_mul_one (A : Mon CpxO) :
    ∀ n : ℤ,
      (ρ_ (A.X.X n)).hom =
        (A.X.X n ◁ ofMonOne A) ≫ ofMonMul A n 0 ≫
          eqToHom (congrArg A.X.X (add_zero n)) := sorry

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
            eqToHom (congrArg A.X.X (Int.add_assoc n m 1).symm)) := sorry

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
    ofMonOne A ≫ f.hom.f 0 = ofMonOne B := sorry

/-- A monoid morphism preserves every extracted homogeneous multiplication. -/
theorem ofMonMap_comm_mul {A B : Mon CpxO} (f : A ⟶ B) :
    ∀ n m : ℤ,
      ofMonMul A n m ≫ f.hom.f (n + m) =
        ((f.hom.f n) ▷ A.X.X m) ≫ (B.X.X n ◁ f.hom.f m) ≫ ofMonMul B n m := sorry

/-- A monoid morphism as a morphism between the recovered differential graded algebras. -/
noncomputable def ofMonMap {A B : Mon CpxO} (f : A ⟶ B) : ofMon A ⟶ ofMon B where
  hom := f.hom
  comm_one := ofMonMap_comm_one f
  comm_mul := ofMonMap_comm_mul f

/-- Recovering differential graded algebra maps preserves identity morphisms. -/
theorem ofMonMap_id (A : Mon CpxO) :
    ofMonMap (𝟙 A) = 𝟙 (ofMon A) := sorry

/-- Recovering differential graded algebra maps preserves composition. -/
theorem ofMonMap_comp {A B D : Mon CpxO} (f : A ⟶ B) (g : B ⟶ D) :
    ofMonMap (f ≫ g) = ofMonMap f ≫ ofMonMap g := sorry

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
      (ofMon A.toMon).one := sorry

/-- The identity cochain map preserves multiplication when comparing a differential graded algebra
with the object recovered from its associated monoid. -/
theorem toMonUnitHom_comm_mul (A : DGA(𝒪)) :
    ∀ n m : ℤ,
      A.mul n m ≫ (𝟙 A.toComplex : A.toComplex ⟶ A.toComplex).f (n + m) =
        (((𝟙 A.toComplex : A.toComplex ⟶ A.toComplex).f n) ▷ A.toComplex.X m) ≫
          ((ofMon A.toMon).toComplex.X n ◁
            (𝟙 A.toComplex : A.toComplex ⟶ A.toComplex).f m) ≫
            (ofMon A.toMon).mul n m := sorry

/-- The forward identity-carrier comparison with the recovered differential graded algebra. -/
noncomputable def toMonUnitHom (A : DGA(𝒪)) : A ⟶ ofMon A.toMon where
  hom := 𝟙 A.toComplex
  comm_one := toMonUnitHom_comm_one A
  comm_mul := toMonUnitHom_comm_mul A

/-- The reverse identity cochain map preserves the unit in the monoid-recovery comparison. -/
theorem toMonUnitInv_comm_one (A : DGA(𝒪)) :
    (ofMon A.toMon).one ≫ (𝟙 A.toComplex : A.toComplex ⟶ A.toComplex).f 0 =
      A.one := sorry

/-- The reverse identity cochain map preserves multiplication in the monoid-recovery comparison. -/
theorem toMonUnitInv_comm_mul (A : DGA(𝒪)) :
    ∀ n m : ℤ,
      (ofMon A.toMon).mul n m ≫
          (𝟙 A.toComplex : A.toComplex ⟶ A.toComplex).f (n + m) =
        (((𝟙 A.toComplex : A.toComplex ⟶ A.toComplex).f n) ▷
            (ofMon A.toMon).toComplex.X m) ≫
          (A.toComplex.X n ◁
            (𝟙 A.toComplex : A.toComplex ⟶ A.toComplex).f m) ≫ A.mul n m := sorry

/-- The inverse identity-carrier comparison with the recovered differential graded algebra. -/
noncomputable def toMonUnitInv (A : DGA(𝒪)) : ofMon A.toMon ⟶ A where
  hom := 𝟙 A.toComplex
  comm_one := toMonUnitInv_comm_one A
  comm_mul := toMonUnitInv_comm_mul A

/-- The two identity-carrier comparisons compose to the identity on the original algebra. -/
theorem toMonUnitHom_inv (A : DGA(𝒪)) :
    toMonUnitHom A ≫ toMonUnitInv A = 𝟙 A := sorry

/-- The two identity-carrier comparisons compose to the identity on the recovered algebra. -/
theorem toMonUnitInv_hom (A : DGA(𝒪)) :
    toMonUnitInv A ≫ toMonUnitHom A = 𝟙 (ofMon A.toMon) := sorry

/-- A differential graded algebra is canonically isomorphic to the object recovered from its
associated monoid. -/
noncomputable def toMonUnitIso (A : DGA(𝒪)) : A ≅ ofMon A.toMon where
  hom := toMonUnitHom A
  inv := toMonUnitInv A
  hom_inv_id := toMonUnitHom_inv A
  inv_hom_id := toMonUnitInv_hom A

/-- The identity carrier map preserves the unit in the comparison from a recovered monoid. -/
theorem toMonCounit_one (A : Mon CpxO) :
    (ofMon A).toMon.mon.one ≫ (Iso.refl A.X).hom = A.mon.one := sorry

/-- The identity carrier map preserves multiplication in the comparison from a recovered monoid. -/
theorem toMonCounit_mul (A : Mon CpxO) :
    (ofMon A).toMon.mon.mul ≫ (Iso.refl A.X).hom =
      ((Iso.refl A.X).hom ⊗ₘ (Iso.refl A.X).hom) ≫ A.mon.mul := sorry

/-- Recovering a differential graded algebra from a monoid and returning to monoids is canonically
isomorphic to the original monoid object. -/
noncomputable def toMonCounitIso (A : Mon CpxO) : (ofMon A).toMon ≅ A :=
  Mon.mkIso (Iso.refl A.X) (toMonCounit_one A) (toMonCounit_mul A)

/-- The algebra-side comparison is natural in differential graded algebra maps. -/
theorem toMonUnitIso_naturality {A B : DGA(𝒪)} (f : A ⟶ B) :
    f ≫ (toMonUnitIso B).hom =
      (toMonUnitIso A).hom ≫ (toMonFunctor ⋙ ofMonFunctor).map f := sorry

/-- The monoid-side comparison is natural in monoid morphisms. -/
theorem toMonCounitIso_naturality {A B : Mon CpxO} (f : A ⟶ B) :
    (ofMonFunctor ⋙ toMonFunctor).map f ≫ (toMonCounitIso B).hom =
      (toMonCounitIso A).hom ≫ f := sorry

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
    (toMonEquivalence (𝒪 := 𝒪)).functor = toMonFunctor := sorry

/-- The inverse functor of `toMonEquivalence` recovers homogeneous DGA data. -/
@[simp]
theorem toMonEquivalence_inverse :
    (toMonEquivalence (𝒪 := 𝒪)).inverse = ofMonFunctor := sorry

/-- The canonical functor from differential graded algebras to cochain monoids is an equivalence. -/
instance toMonFunctor_isEquivalence :
    (toMonFunctor (𝒪 := 𝒪)).IsEquivalence := sorry

end

end SheafOfModules.RingedSite.DifferentialGradedAlgebra

end
