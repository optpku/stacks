/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.Algebra.Homology.DifferentialGradedAlgebra.Commutative.Category
public import ReasLib.Algebra.Homology.DifferentialGradedAlgebra.Nonnegative
public import ReasLib.RingTheory.DividedPowers.GradedAlgebra.Category

/-!
# Chain differential graded algebras with divided powers

This file owns the reusable chain-DGA compatibility structure and its morphisms. It is independent
of Tate resolutions: resolutions, base change, and homology descent all consume this layer.
-/

@[expose] public section

noncomputable section

open CategoryTheory
open scoped DirectSum

universe u v

namespace ChainDGAlgebra

variable {R : Type u} [CommRing R]

namespace DividedPowers

/-- Definition 23.6.5 (Tag 09PJ): compatibility of graded divided powers with a chain
differential on the canonical positive-even part. -/
@[mk_iff isCompatible_iff, stacks 09PJ "chain differential compatibility"]
class IsCompatible (A : ChainDGAlgebra.{u, v} R) [A.IsStrictlyCommutative]
    (gamma : NonnegGradedAlgebra.DividedPowers A.nonnegativePart) : Prop where
  /-- The differential of `gamma n x` is `d x * gamma (n - 1) x`. The even factor is written
  first because the parity API exposes even-by-odd multiplication. -/
  differential_gamma (n : ℕ+) (x : A.nonnegativePart.evenPositivePart) :
    A.positiveEvenDifferential (gamma.gammaPos n x) =
      A.nonnegativePart.evenMulOdd (gamma ((n : ℕ) - 1) x)
        (A.positiveEvenDifferential x)

end DividedPowers

end ChainDGAlgebra

/-- Definition 23.6.5 (Tag 09PJ): a nonnegative strictly commutative chain DGA equipped with
divided powers compatible with its differential. -/
@[stacks 09PJ "bundled chain differential graded algebra"]
structure DividedPowerChainAlgebra (R : Type u) [CommRing R] where
  /-- The underlying chain differential graded algebra. -/
  toChainDGAlgebra : ChainDGAlgebra.{u, v} R
  /-- Strict graded commutativity of the underlying chain DGA. -/
  [isStrictlyCommutative : toChainDGAlgebra.IsStrictlyCommutative]
  /-- The chain DGA is supported in nonnegative degrees. -/
  [isNonnegative : toChainDGAlgebra.IsNonnegative]
  /-- Divided powers on the positive even part of the nonnegative restriction. -/
  gamma : NonnegGradedAlgebra.DividedPowers toChainDGAlgebra.nonnegativePart
  /-- The divided powers are compatible with the differential. -/
  compatible : ChainDGAlgebra.DividedPowers.IsCompatible toChainDGAlgebra gamma

attribute [instance] DividedPowerChainAlgebra.isStrictlyCommutative
attribute [instance] DividedPowerChainAlgebra.isNonnegative
attribute [instance] DividedPowerChainAlgebra.compatible

namespace DividedPowerChainAlgebra

variable {R : Type u} [CommRing R]

/-- Forget the divided powers and nonnegative support of an object, retaining strict graded
commutativity of its underlying chain DGA. -/
@[stacks 09PJ "infrastructure: strict chain DGA underlying a divided-power chain DGA"]
def toStrict (A : DividedPowerChainAlgebra.{u, v} R) : ChainDGAlgebra.Strict.{u, v} R where
  toChainDGAlgebra := A.toChainDGAlgebra
  isStrictlyCommutative := A.isStrictlyCommutative

/-- The chain DGA underlying `toStrict A` is the chain DGA underlying `A`. -/
@[simp] theorem toStrict_toChainDGAlgebra (A : DividedPowerChainAlgebra.{u, v} R) :
    A.toStrict.toChainDGAlgebra = A.toChainDGAlgebra := sorry

/-- The nonnegative graded algebra with divided powers underlying a divided-power chain DGA. -/
def toGradedAlgebra (A : DividedPowerChainAlgebra.{u, v} R) :
    DividedPowerGradedAlgebra.{u, v} R :=
  DividedPowerGradedAlgebra.of A.toChainDGAlgebra.nonnegativePart A.gamma

variable {A B : DividedPowerChainAlgebra.{u, v} R}

/-- A homomorphism of nonnegative strictly commutative chain DGAs preserving divided powers. -/
@[stacks 09PJ "morphism of divided-power chain DGAs"]
structure Hom (A B : DividedPowerChainAlgebra.{u, v} R) where
  /-- The underlying chain-DGA homomorphism. -/
  toChainHom : ChainDGAlgebra.Hom A.toChainDGAlgebra B.toChainDGAlgebra
  /-- Divided powers are preserved on the positive even direct sum. -/
  map_gamma (n : ℕ)
    (x : A.toChainDGAlgebra.nonnegativePart.evenPositivePart) :
    toChainHom.nonnegativePart.evenMap (A.gamma n x) =
      B.gamma n (toChainHom.nonnegativePart.evenPositiveMap x)

namespace Hom

/-- A divided-power chain-DGA homomorphism acts degreewise on homogeneous elements. -/
instance : CoeFun (Hom A B) (fun _ ↦ ∀ n : ℤ,
    A.toChainDGAlgebra.X n → B.toChainDGAlgebra.X n) where
  coe f := f.toChainHom

/-- Degreewise evaluation is evaluation of the underlying chain-DGA homomorphism. -/
@[simp] theorem coe_apply (f : Hom A B) (n : ℤ) (x : A.toChainDGAlgebra.X n) :
    f n x = f.toChainHom n x := sorry

/-- A divided-power chain-DGA homomorphism commutes with the differential. -/
@[simp] theorem map_d (f : Hom A B) (n : ℤ) (x : A.toChainDGAlgebra.X n) :
    f (n - 1) (A.toChainDGAlgebra.d n x) =
      B.toChainDGAlgebra.d n (f n x) := sorry

/-- A divided-power chain-DGA homomorphism preserves the homogeneous unit. -/
@[simp] theorem map_one (f : Hom A B) :
    f 0 A.toChainDGAlgebra.one = B.toChainDGAlgebra.one := sorry

/-- A divided-power chain-DGA homomorphism preserves homogeneous multiplication. -/
@[simp] theorem map_mul (f : Hom A B) (n m : ℤ)
    (x : A.toChainDGAlgebra.X n) (y : A.toChainDGAlgebra.X m) :
    f (n + m) (A.toChainDGAlgebra.mul n m x y) =
      B.toChainDGAlgebra.mul n m (f n x) (f m y) := sorry

/-- The identity chain-DGA homomorphism preserves divided powers. -/
theorem id_map_gamma (A : DividedPowerChainAlgebra.{u, v} R) (n : ℕ)
    (x : A.toChainDGAlgebra.nonnegativePart.evenPositivePart) :
    (ChainDGAlgebra.Hom.id A.toChainDGAlgebra).nonnegativePart.evenMap (A.gamma n x) =
      A.gamma n
        ((ChainDGAlgebra.Hom.id A.toChainDGAlgebra).nonnegativePart.evenPositiveMap x) := sorry

/-- The identity homomorphism of a divided-power chain DGA. -/
def id (A : DividedPowerChainAlgebra.{u, v} R) : Hom A A where
  toChainHom := ChainDGAlgebra.Hom.id A.toChainDGAlgebra
  map_gamma := id_map_gamma A

/-- A composite of divided-power chain-DGA homomorphisms preserves divided powers. -/
theorem comp_map_gamma {C : DividedPowerChainAlgebra.{u, v} R}
    (g : Hom B C) (f : Hom A B) (n : ℕ)
    (x : A.toChainDGAlgebra.nonnegativePart.evenPositivePart) :
    (ChainDGAlgebra.Hom.comp g.toChainHom f.toChainHom).nonnegativePart.evenMap
        (A.gamma n x) =
      C.gamma n
        ((ChainDGAlgebra.Hom.comp g.toChainHom f.toChainHom).nonnegativePart.evenPositiveMap x) := sorry

/-- Composition of divided-power chain-DGA homomorphisms. -/
def comp {C : DividedPowerChainAlgebra.{u, v} R} (g : Hom B C) (f : Hom A B) : Hom A C where
  toChainHom := ChainDGAlgebra.Hom.comp g.toChainHom f.toChainHom
  map_gamma := comp_map_gamma g f

/-- Divided-power chain-DGA homomorphisms are determined by their underlying chain-DGA maps. -/
theorem ext_toChainHom {f g : Hom A B} (h : f.toChainHom = g.toChainHom) : f = g := sorry

/-- Divided-power chain-DGA homomorphisms are determined degreewise. -/
@[ext] theorem ext {f g : Hom A B}
    (h : ∀ (n : ℤ) (x : A.toChainDGAlgebra.X n), f n x = g n x) : f = g := sorry

/-- The identity divided-power chain-DGA homomorphism acts identically in every degree. -/
@[simp] theorem id_apply (A : DividedPowerChainAlgebra.{u, v} R) (n : ℤ)
    (x : A.toChainDGAlgebra.X n) : id A n x = x := sorry

/-- Composition of divided-power chain-DGA homomorphisms acts degreewise by composition. -/
@[simp] theorem comp_apply {C : DividedPowerChainAlgebra.{u, v} R}
    (g : Hom B C) (f : Hom A B) (n : ℤ) (x : A.toChainDGAlgebra.X n) :
    comp g f n x = g n (f n x) := sorry

/-- Composing with the identity on the source leaves a divided-power chain-DGA map unchanged. -/
@[simp] theorem id_comp (f : Hom A B) : comp f (id A) = f := sorry

/-- Composing with the identity on the target leaves a divided-power chain-DGA map unchanged. -/
@[simp] theorem comp_id (f : Hom A B) : comp (id B) f = f := sorry

/-- Composition of divided-power chain-DGA homomorphisms is associative. -/
theorem assoc {C D : DividedPowerChainAlgebra.{u, v} R}
    (f : Hom A B) (g : Hom B C) (h : Hom C D) :
    comp h (comp g f) = comp (comp h g) f := sorry

/-- The underlying chain-DGA map of the identity is the identity. -/
@[simp] theorem toChainHom_id (A : DividedPowerChainAlgebra.{u, v} R) :
    (id A).toChainHom = 𝟙 A.toChainDGAlgebra := sorry

/-- The underlying chain-DGA map of a composite is the composite of the underlying maps. -/
@[simp] theorem toChainHom_comp {C : DividedPowerChainAlgebra.{u, v} R}
    (f : Hom A B) (g : Hom B C) :
    (comp g f).toChainHom =
      ChainDGAlgebra.Hom.comp g.toChainHom f.toChainHom := sorry

/-- Forget divided-power compatibility from a morphism while retaining its strict chain-DGA
source and target. -/
def toStrictHom (f : Hom A B) : A.toStrict ⟶ B.toStrict :=
  f.toChainHom

/-- The strict chain-DGA map underlying a divided-power morphism acts degreewise as that
morphism. -/
@[simp] theorem toStrictHom_apply (f : Hom A B) (n : ℤ)
    (x : A.toChainDGAlgebra.X n) :
    f.toStrictHom n x = f n x := sorry

/-- Forgetting to strict chain DGAs preserves identities. -/
@[simp] theorem toStrictHom_id (A : DividedPowerChainAlgebra.{u, v} R) :
    (id A).toStrictHom = 𝟙 A.toStrict := sorry

/-- Forgetting to strict chain DGAs preserves composition. -/
@[simp] theorem toStrictHom_comp {C : DividedPowerChainAlgebra.{u, v} R}
    (f : Hom A B) (g : Hom B C) :
    (comp g f).toStrictHom = f.toStrictHom ≫ g.toStrictHom := sorry

/-- The underlying divided-power homomorphism between the nonnegative graded algebras. -/
def toGradedHom (f : Hom A B) : A.toGradedAlgebra ⟶ B.toGradedAlgebra where
  toGradedHom := f.toChainHom.nonnegativePart
  map_gamma := f.map_gamma

/-- The underlying graded divided-power map acts by the original chain map in every
nonnegative degree. -/
@[simp] theorem toGradedHom_apply (f : Hom A B) (n : ℕ)
    (x : A.toChainDGAlgebra.nonnegativePiece n) :
    f.toGradedHom.toGradedHom.map n x = f n x := sorry

/-- Restricting the identity chain map gives the identity graded divided-power map. -/
@[simp] theorem toGradedHom_id (A : DividedPowerChainAlgebra.{u, v} R) :
    (id A).toGradedHom = 𝟙 A.toGradedAlgebra := sorry

/-- Restriction to the nonnegative graded divided-power algebra preserves composition. -/
@[simp] theorem toGradedHom_comp {C : DividedPowerChainAlgebra.{u, v} R}
    (f : Hom A B) (g : Hom B C) :
    (comp g f).toGradedHom = f.toGradedHom ≫ g.toGradedHom := sorry

/-- A divided-power chain-DGA homomorphism is surjective in every degree. -/
def Surjective (f : Hom A B) : Prop :=
  f.toChainHom.Surjective

/-- A divided-power chain-DGA homomorphism is injective in every degree. -/
def Injective (f : Hom A B) : Prop :=
  f.toChainHom.Injective

/-- A divided-power chain-DGA homomorphism is bijective in every degree. -/
def Bijective (f : Hom A B) : Prop :=
  f.Injective ∧ f.Surjective

/-- The identity divided-power chain-DGA homomorphism is degreewise surjective. -/
theorem id_surjective (A : DividedPowerChainAlgebra.{u, v} R) : (id A).Surjective := sorry

/-- The identity divided-power chain-DGA homomorphism is degreewise injective. -/
theorem id_injective (A : DividedPowerChainAlgebra.{u, v} R) : (id A).Injective := sorry

/-- The identity divided-power chain-DGA homomorphism is degreewise bijective. -/
theorem id_bijective (A : DividedPowerChainAlgebra.{u, v} R) : (id A).Bijective := sorry

/-- A composite of degreewise-surjective divided-power chain-DGA homomorphisms is surjective. -/
theorem comp_surjective {C : DividedPowerChainAlgebra.{u, v} R}
    {g : Hom B C} {f : Hom A B} (hg : g.Surjective) (hf : f.Surjective) :
    (comp g f).Surjective := sorry

/-- A composite of degreewise-injective divided-power chain-DGA homomorphisms is injective. -/
theorem comp_injective {C : DividedPowerChainAlgebra.{u, v} R}
    {g : Hom B C} {f : Hom A B} (hg : g.Injective) (hf : f.Injective) :
    (comp g f).Injective := sorry

/-- A composite of degreewise-bijective divided-power chain-DGA homomorphisms is bijective. -/
theorem comp_bijective {C : DividedPowerChainAlgebra.{u, v} R}
    {g : Hom B C} {f : Hom A B} (hg : g.Bijective) (hf : f.Bijective) :
    (comp g f).Bijective := sorry

end Hom

end DividedPowerChainAlgebra

/-- Divided-power chain DGAs and their structure-preserving homomorphisms form a category. -/
instance {R : Type u} [CommRing R] :
    CategoryTheory.Category (DividedPowerChainAlgebra.{u, v} R) where
  Hom := DividedPowerChainAlgebra.Hom
  id := DividedPowerChainAlgebra.Hom.id
  comp f g := DividedPowerChainAlgebra.Hom.comp g f
  id_comp := DividedPowerChainAlgebra.Hom.id_comp
  comp_id := DividedPowerChainAlgebra.Hom.comp_id
  assoc := DividedPowerChainAlgebra.Hom.assoc

namespace DividedPowerChainAlgebra

/-- Forget divided powers and nonnegative support, retaining strict graded commutativity. -/
@[stacks 09PJ "infrastructure: forgetful functor to strict chain DGAs"]
def forgetStrict (R : Type u) [CommRing R] :
    DividedPowerChainAlgebra.{u, v} R ⥤ ChainDGAlgebra.Strict.{u, v} R where
  obj A := A.toStrict
  map f := f.toStrictHom
  map_id := Hom.toStrictHom_id
  map_comp := Hom.toStrictHom_comp

/-- The strict forgetful functor sends an object to its underlying strict chain DGA. -/
@[simp] theorem forgetStrict_obj {R : Type u} [CommRing R]
    (A : DividedPowerChainAlgebra.{u, v} R) :
    (forgetStrict R).obj A = A.toStrict := sorry

/-- The strict forgetful functor sends a morphism to its underlying chain-DGA map. -/
@[simp] theorem forgetStrict_map {R : Type u} [CommRing R]
    {A B : DividedPowerChainAlgebra.{u, v} R} (f : A ⟶ B) :
    (forgetStrict R).map f = f.toStrictHom := sorry

/-- Forget the divided powers, support, and strict commutativity, retaining the underlying chain
DGA. -/
@[stacks 09PJ "infrastructure: forgetful functor to chain differential graded algebras"]
def forget (R : Type u) [CommRing R] :
    DividedPowerChainAlgebra.{u, v} R ⥤ ChainDGAlgebra.{u, v} R :=
  forgetStrict R ⋙ ChainDGAlgebra.Strict.forget R

/-- The forgetful functor sends an object to its underlying chain DGA. -/
@[simp] theorem forget_obj {R : Type u} [CommRing R]
    (A : DividedPowerChainAlgebra.{u, v} R) :
    (forget R).obj A = A.toChainDGAlgebra := sorry

/-- The forgetful functor sends a morphism to its underlying chain-DGA map. -/
@[simp] theorem forget_map {R : Type u} [CommRing R]
    {A B : DividedPowerChainAlgebra.{u, v} R} (f : A ⟶ B) :
    (forget R).map f = f.toChainHom := sorry

/-- Forget the differential, retaining the nonnegative graded algebra and its divided powers. -/
def toGraded (R : Type u) [CommRing R] :
    DividedPowerChainAlgebra.{u, v} R ⥤ DividedPowerGradedAlgebra.{u, v} R where
  obj A := A.toGradedAlgebra
  map f := f.toGradedHom
  map_id := Hom.toGradedHom_id
  map_comp := Hom.toGradedHom_comp

/-- Forget the differential and divided powers, retaining the nonnegative graded algebra. -/
def toNonnegGraded (R : Type u) [CommRing R] :
    DividedPowerChainAlgebra.{u, v} R ⥤ NonnegGradedAlgebra.{u, v} R :=
  toGraded R ⋙ DividedPowerGradedAlgebra.forget R

/-- The map of `toGraded` is restriction of a chain map with its divided-power compatibility. -/
@[simp] theorem toGraded_map {R : Type u} [CommRing R]
    {A B : DividedPowerChainAlgebra.{u, v} R} (f : A ⟶ B) :
    (toGraded R).map f = f.toGradedHom := sorry

/-- The map of `toNonnegGraded` is the nonnegative restriction of the underlying chain map. -/
@[simp] theorem toNonnegGraded_map {R : Type u} [CommRing R]
    {A B : DividedPowerChainAlgebra.{u, v} R} (f : A ⟶ B) :
    (toNonnegGraded R).map f = f.toChainHom.nonnegativePart := sorry

end DividedPowerChainAlgebra

#synth CategoryTheory.Category (DividedPowerChainAlgebra ℤ)
