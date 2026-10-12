/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.AlgebraicGeometry.Spec
public import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects
public import Mathlib.RingTheory.GradedAlgebra.Basic
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.TopSections
public import stacks_project.Chap66.Lemma_66_27_3_Space
public import stacks_project.Chap66.Lemma_66_29_2_Pullback
public import stacks_project.Chap69.Lemma_69_16_2_ToSpec
public import stacks_project.Chap69.Lemma_69_17_2_Pullback

/-!
# Pullbacks of affine tilde graded algebras on algebraic spaces

This module identifies a degreewise family `𝓑` of modules on an algebraic space with the
pullback of the affine tilde algebra of a nonnegatively graded algebra, including the
induced graded `𝒪_X`-algebra structure.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open SheafOfModules

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

variable {S : Scheme.{u}}

/-- The type-valued sheaf underlying the structure module of an algebraic space. -/
def unitCarrierIso (X : AlgebraicSpace S) :
    (Sheaf.InternalModule.ToInternal.underlying (structureSheaf X)).obj
      (SheafOfModules.unit (structureSheaf X)) ≅
      (sheafCompose (smallEtaleTopology X) (forget RingCat.{u})).obj (structureSheaf X) where
  hom := { hom := { app := fun _ ↦ 𝟙 _, naturality := fun _ _ _ ↦ sorry } }
  inv := { hom := { app := fun _ ↦ 𝟙 _, naturality := fun _ _ _ ↦ sorry } }
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The type-valued sheaf underlying the unit of `f⁻¹ 𝒪_Y`. -/
def inverseImageUnitCarrierIso {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    (Sheaf.InternalModule.ToInternal.underlying
          ((ringedToposHom f).toTopos.ringInverseImage.obj (structureSheaf Y))).obj
      (SheafOfModules.unit
        ((ringedToposHom f).toTopos.ringInverseImage.obj (structureSheaf Y))) ≅
      (sheafCompose (smallEtaleTopology X) (forget RingCat.{u})).obj
        ((ringedToposHom f).toTopos.ringInverseImage.obj (structureSheaf Y)) where
  hom := { hom := { app := fun _ ↦ 𝟙 _, naturality := fun _ _ _ ↦ sorry } }
  inv := { hom := { app := fun _ ↦ 𝟙 _, naturality := fun _ _ _ ↦ sorry } }
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- Inverse image of the structure module of `Y` is the unit module of `f⁻¹ 𝒪_Y`. -/
def moduleInverseImageUnitIso {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    ((ringedToposHom f).toTopos.moduleInverseImage (structureSheaf Y)).obj
        (SheafOfModules.unit (structureSheaf Y)) ≅
      SheafOfModules.unit
        ((ringedToposHom f).toTopos.ringInverseImage.obj (structureSheaf Y)) where
  hom :=
    Sheaf.InternalModule.homOfUnderlying
      ((ringedToposHom f).toTopos.ringInverseImage.obj (structureSheaf Y))
      (((ringedToposHom f).toTopos.moduleInverseImageForgetIso (structureSheaf Y)).hom.app
          (SheafOfModules.unit (structureSheaf Y)) ≫
        (ringedToposHom f).toTopos.inverseImage.map (unitCarrierIso Y).hom ≫
        (ringedToposHom f).toTopos.ringInverseImageForgetIso.inv.app (structureSheaf Y) ≫
        (inverseImageUnitCarrierIso f).inv)
      sorry sorry
  inv :=
    Sheaf.InternalModule.homOfUnderlying
      ((ringedToposHom f).toTopos.ringInverseImage.obj (structureSheaf Y))
      ((inverseImageUnitCarrierIso f).hom ≫
        (ringedToposHom f).toTopos.ringInverseImageForgetIso.hom.app (structureSheaf Y) ≫
        (ringedToposHom f).toTopos.inverseImage.map (unitCarrierIso Y).inv ≫
        ((ringedToposHom f).toTopos.moduleInverseImageForgetIso (structureSheaf Y)).inv.app
          (SheafOfModules.unit (structureSheaf Y)))
      sorry sorry
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The free rank-one module `𝒪_X` maps to the scalar extension of `f⁻¹ 𝒪_Y`. -/
def extendScalarsUnitFromStructure {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    SheafOfModules.unit (structureSheaf X) ⟶
      (SheafOfModules.ChangeOfRings.extendScalars (ringedToposHom f).structureMap).obj
        (SheafOfModules.unit
          ((ringedToposHom f).toTopos.ringInverseImage.obj (structureSheaf Y))) :=
  let α := (ringedToposHom f).structureMap
  let Rinv := (ringedToposHom f).toTopos.ringInverseImage.obj (structureSheaf Y)
  let M := (SheafOfModules.ChangeOfRings.extendScalars α).obj (SheafOfModules.unit Rinv)
  let s :=
    ((SheafOfModules.restrictScalars α).obj M).unitHomEquiv
      ((SheafOfModules.ChangeOfRings.extendRestrictAdjunction α).unit.app
        (SheafOfModules.unit Rinv))
  M.unitHomEquiv.symm (PresheafOfModules.sectionsMk (fun U ↦ s.val U) fun _ _ h ↦ s.property h)

/-- The canonical map `𝒪_X ⟶ f^* 𝒪_Y`. -/
def structureModulePullbackInv {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    SheafOfModules.unit (structureSheaf X) ⟶
      (pullback f).obj (SheafOfModules.unit (structureSheaf Y)) :=
  extendScalarsUnitFromStructure f ≫
    (SheafOfModules.ChangeOfRings.extendScalars (ringedToposHom f).structureMap).map
      (moduleInverseImageUnitIso f).inv ≫
    (pullbackIsoTopos f).inv.app (SheafOfModules.unit (structureSheaf Y))

/-- Pullback of a compatible section along a morphism of algebraic spaces. -/
def sectionsPullback {X Y : AlgebraicSpace S} (f : X ⟶ Y) (F : Y.Modules)
    (s : F.sections) : ((pullback f).obj F).sections :=
  SheafOfModules.sectionsMap
    ((pullback f).map ((SheafOfModules.unitHomEquiv F).symm s))
    (SheafOfModules.unitHomEquiv ((pullback f).obj (SheafOfModules.unit (structureSheaf Y)))
      (structureModulePullbackInv f))

namespace PullbackTilde

/-- The affine tilde global section of a homogeneous element of a graded algebra. -/
def affineTildeSection {A : Type u} [CommRing A] {B : Type u} [CommRing B] [Algebra A B]
    (𝒜 : ℕ → Submodule A B) (n : ℕ) (b : 𝒜 n) :
    (modulesSpecToSheaf.obj (tilde (ModuleCat.of (CommRingCat.of A) (𝒜 n)))).presheaf.obj
      (Opposite.op ⊤) :=
  (tilde.isoTop (ModuleCat.of (CommRingCat.of A) (𝒜 n))).hom b

/-- `affineTildeSection` is the image of a homogeneous element under `tilde.isoTop`. -/
theorem affineTildeSection_eq {A : Type u} [CommRing A] {B : Type u} [CommRing B]
    [Algebra A B] (𝒜 : ℕ → Submodule A B) (n : ℕ) (b : 𝒜 n) :
    affineTildeSection 𝒜 n b = (tilde.isoTop (ModuleCat.of (CommRingCat.of A) (𝒜 n))).hom b :=
  sorry

/-- The compatible scheme-module section determined by a homogeneous affine tilde value. -/
def affineTildeCompatibleSection {A : Type u} [CommRing A] {B : Type u} [CommRing B]
    [Algebra A B] (𝒜 : ℕ → Submodule A B) (n : ℕ) (b : 𝒜 n) :
    ((tilde.functor (CommRingCat.of A)).obj (ModuleCat.of (CommRingCat.of A) (𝒜 n))).sections :=
  RingedSpace.sectionFromTop
    ((tilde.functor (CommRingCat.of A)).obj (ModuleCat.of (CommRingCat.of A) (𝒜 n)))
    (affineTildeSection 𝒜 n b)

/-- A graded `𝒪_X`-algebra given degreewise as modules on an algebraic space. -/
structure OXGradedAlgebra {X : AlgebraicSpace S} (𝓑 : ℤ → X.Modules) where
  /-- The local unit section in degree zero. -/
  one : ∀ U : (smallEtaleSite X)ᵒᵖ, (𝓑 0).val.obj U
  /-- The local `𝒪_X`-bilinear multiplication. -/
  mul : ∀ (U : (smallEtaleSite X)ᵒᵖ) (n m : ℤ),
    (𝓑 n).val.obj U → (𝓑 m).val.obj U → (𝓑 (n + m)).val.obj U
  /-- The unit section is compatible with restriction. -/
  map_one : ∀ {U V : (smallEtaleSite X)ᵒᵖ} (i : U ⟶ V),
    ((𝓑 0).val.map i).hom (one U) = one V
  /-- Multiplication is compatible with restriction. -/
  map_mul : ∀ {U V : (smallEtaleSite X)ᵒᵖ} (i : U ⟶ V) (n m : ℤ)
    (a : (𝓑 n).val.obj U) (b : (𝓑 m).val.obj U),
    ((𝓑 (n + m)).val.map i).hom (mul U n m a b) =
      mul V n m (((𝓑 n).val.map i).hom a) (((𝓑 m).val.map i).hom b)
  /-- Multiplication is additive in the first argument. -/
  mul_add : ∀ (U : (smallEtaleSite X)ᵒᵖ) (n m : ℤ)
    (a₁ a₂ : (𝓑 n).val.obj U) (b : (𝓑 m).val.obj U),
    mul U n m (a₁ + a₂) b = mul U n m a₁ b + mul U n m a₂ b
  /-- Multiplication is additive in the second argument. -/
  add_mul : ∀ (U : (smallEtaleSite X)ᵒᵖ) (n m : ℤ)
    (a : (𝓑 n).val.obj U) (b₁ b₂ : (𝓑 m).val.obj U),
    mul U n m a (b₁ + b₂) = mul U n m a b₁ + mul U n m a b₂
  /-- Multiplication is `𝒪_X`-linear in the first argument. -/
  smul_mul : ∀ (U : (smallEtaleSite X)ᵒᵖ) (n m : ℤ)
    (r : (structureSheaf X).obj.obj U) (a : (𝓑 n).val.obj U) (b : (𝓑 m).val.obj U),
    mul U n m (r • a) b = r • mul U n m a b
  /-- Multiplication is `𝒪_X`-linear in the second argument. -/
  mul_smul : ∀ (U : (smallEtaleSite X)ᵒᵖ) (n m : ℤ)
    (r : (structureSheaf X).obj.obj U) (a : (𝓑 n).val.obj U) (b : (𝓑 m).val.obj U),
    mul U n m a (r • b) = r • mul U n m a b
  /-- Multiplication is associative on local sections. -/
  mul_assoc : ∀ (U : (smallEtaleSite X)ᵒᵖ) (i j k : ℤ)
    (a : (𝓑 i).val.obj U) (b : (𝓑 j).val.obj U) (c : (𝓑 k).val.obj U),
    HEq (mul U (i + j) k (mul U i j a b) c) (mul U i (j + k) a (mul U j k b c))
  /-- The unit is a left identity. -/
  one_mul : ∀ (U : (smallEtaleSite X)ᵒᵖ) (n : ℤ) (a : (𝓑 n).val.obj U),
    HEq (mul U 0 n (one U) a) a
  /-- The unit is a right identity. -/
  mul_one : ∀ (U : (smallEtaleSite X)ᵒᵖ) (n : ℤ) (a : (𝓑 n).val.obj U),
    HEq (mul U n 0 a (one U)) a

namespace OXGradedAlgebra

/-- Constructs a graded algebra from local unit, multiplication, restriction, associativity,
and unit laws. -/
def ofComponents {X : AlgebraicSpace S} (𝓑 : ℤ → X.Modules)
    (one : ∀ U : (smallEtaleSite X)ᵒᵖ, (𝓑 0).val.obj U)
    (mul : ∀ (U : (smallEtaleSite X)ᵒᵖ) (n m : ℤ),
      (𝓑 n).val.obj U → (𝓑 m).val.obj U → (𝓑 (n + m)).val.obj U)
    (map_one : ∀ {U V : (smallEtaleSite X)ᵒᵖ} (i : U ⟶ V),
      ((𝓑 0).val.map i).hom (one U) = one V)
    (map_mul : ∀ {U V : (smallEtaleSite X)ᵒᵖ} (i : U ⟶ V) (n m : ℤ)
      (a : (𝓑 n).val.obj U) (b : (𝓑 m).val.obj U),
      ((𝓑 (n + m)).val.map i).hom (mul U n m a b) =
        mul V n m (((𝓑 n).val.map i).hom a) (((𝓑 m).val.map i).hom b))
    (mul_add : ∀ (U : (smallEtaleSite X)ᵒᵖ) (n m : ℤ)
      (a₁ a₂ : (𝓑 n).val.obj U) (b : (𝓑 m).val.obj U),
      mul U n m (a₁ + a₂) b = mul U n m a₁ b + mul U n m a₂ b)
    (add_mul : ∀ (U : (smallEtaleSite X)ᵒᵖ) (n m : ℤ)
      (a : (𝓑 n).val.obj U) (b₁ b₂ : (𝓑 m).val.obj U),
      mul U n m a (b₁ + b₂) = mul U n m a b₁ + mul U n m a b₂)
    (smul_mul : ∀ (U : (smallEtaleSite X)ᵒᵖ) (n m : ℤ)
      (r : (structureSheaf X).obj.obj U) (a : (𝓑 n).val.obj U) (b : (𝓑 m).val.obj U),
      mul U n m (r • a) b = r • mul U n m a b)
    (mul_smul : ∀ (U : (smallEtaleSite X)ᵒᵖ) (n m : ℤ)
      (r : (structureSheaf X).obj.obj U) (a : (𝓑 n).val.obj U) (b : (𝓑 m).val.obj U),
      mul U n m a (r • b) = r • mul U n m a b)
    (mul_assoc : ∀ (U : (smallEtaleSite X)ᵒᵖ) (i j k : ℤ)
      (a : (𝓑 i).val.obj U) (b : (𝓑 j).val.obj U) (c : (𝓑 k).val.obj U),
      HEq (mul U (i + j) k (mul U i j a b) c) (mul U i (j + k) a (mul U j k b c)))
    (one_mul : ∀ (U : (smallEtaleSite X)ᵒᵖ) (n : ℤ) (a : (𝓑 n).val.obj U),
      HEq (mul U 0 n (one U) a) a)
    (mul_one : ∀ (U : (smallEtaleSite X)ᵒᵖ) (n : ℤ) (a : (𝓑 n).val.obj U),
      HEq (mul U n 0 a (one U)) a) :
    OXGradedAlgebra 𝓑 :=
  { one := one
    mul := mul
    map_one := map_one
    map_mul := map_mul
    mul_add := mul_add
    add_mul := add_mul
    smul_mul := smul_mul
    mul_smul := mul_smul
    mul_assoc := mul_assoc
    one_mul := one_mul
    mul_one := mul_one }

/-- The compatible global unit section of a graded algebra. -/
def oneSection {X : AlgebraicSpace S} {𝓑 : ℤ → X.Modules} (alg : OXGradedAlgebra 𝓑) :
    (𝓑 0).sections :=
  (𝓑 0).val.sectionsMk alg.one fun _ _ i ↦ alg.map_one i

/-- The unit, multiplication, restriction, associativity, and unit laws of a graded algebra. -/
theorem spec {X : AlgebraicSpace S} {𝓑 : ℤ → X.Modules} (alg : OXGradedAlgebra 𝓑) :
    (∀ {U V : (smallEtaleSite X)ᵒᵖ} (i : U ⟶ V),
      ((𝓑 0).val.map i).hom (alg.one U) = alg.one V) ∧
    (∀ {U V : (smallEtaleSite X)ᵒᵖ} (i : U ⟶ V) (n m : ℤ)
      (a : (𝓑 n).val.obj U) (b : (𝓑 m).val.obj U),
      ((𝓑 (n + m)).val.map i).hom (alg.mul U n m a b) =
        alg.mul V n m (((𝓑 n).val.map i).hom a) (((𝓑 m).val.map i).hom b)) ∧
    (∀ (U : (smallEtaleSite X)ᵒᵖ) (i j k : ℤ)
      (a : (𝓑 i).val.obj U) (b : (𝓑 j).val.obj U) (c : (𝓑 k).val.obj U),
      HEq (alg.mul U (i + j) k (alg.mul U i j a b) c)
        (alg.mul U i (j + k) a (alg.mul U j k b c))) ∧
    (∀ (U : (smallEtaleSite X)ᵒᵖ) (n : ℤ) (a : (𝓑 n).val.obj U),
      HEq (alg.mul U 0 n (alg.one U) a) a) ∧
    (∀ (U : (smallEtaleSite X)ᵒᵖ) (n : ℤ) (a : (𝓑 n).val.obj U),
      HEq (alg.mul U n 0 a (alg.one U)) a) :=
  sorry

end OXGradedAlgebra

/-- Affine tilde sections transported along `tildeIso` to compatible sections of the affine
model on `ofOver (Over.mk σA)`, using the identification of Zariski-top sections of
`toScheme` with identity-object étale sections. -/
def tildeBSectionFromAffine {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    (𝒜 : ℕ → Submodule A B) (σA : Spec (CommRingCat.of A) ⟶ S)
    (tildeB : ℕ → (ofOver (Over.mk σA)).Modules)
    (tildeIso : ∀ n : ℕ,
      (toScheme (Over.mk σA)).obj (tildeB n) ≅
        (tilde.functor (CommRingCat.of A)).obj (ModuleCat.of (CommRingCat.of A) (𝒜 n)))
    (toSchemeTopIso : ∀ n : ℕ,
      ((toScheme (Over.mk σA)).obj (tildeB n)).val.obj
          (Opposite.op (⊤ : Opens (Over.mk σA).left)) ≅
        (tildeB n).val.obj (Opposite.op (smallEtaleSite.id (Over.mk σA))))
    (n : ℕ) (b : 𝒜 n) : (tildeB n).sections :=
  (tildeB n).val.sectionsMk
    (fun V ↦
      ((tildeB n).val.map (smallEtaleSite.homToId (Over.mk σA) V.unop).op)
        ((toSchemeTopIso n).hom
          ((sectionsMap (tildeIso n).inv (affineTildeCompatibleSection 𝒜 n b)).1
            (Opposite.op (⊤ : Opens (Over.mk σA).left)))))
    sorry

/-- Comparison data identifying a degreewise family of modules on an algebraic space with the
pullback of the affine tilde algebra of a nonnegatively graded algebra. -/
structure Comparison {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    (𝒜 : ℕ → Submodule A B) [GradedAlgebra 𝒜] {X : AlgebraicSpace S}
    (σA : Spec (CommRingCat.of A) ⟶ S) (f : X ⟶ ofOver (Over.mk σA))
    (𝓑 : ℤ → X.Modules) extends OXGradedAlgebra 𝓑 where
  /-- Affine models of the nonnegative homogeneous pieces, as modules on `ofOver (Over.mk σA)`. -/
  tildeB : ℕ → (ofOver (Over.mk σA)).Modules
  /-- Degreewise identification of `toScheme` of the affine model with the associated sheaf of
  the homogeneous piece. -/
  tildeIso : ∀ n : ℕ,
    (toScheme (Over.mk σA)).obj (tildeB n) ≅
      (tilde.functor (CommRingCat.of A)).obj (ModuleCat.of (CommRingCat.of A) (𝒜 n))
  /-- Identification of Zariski-top sections of `toScheme` of the affine model with
  identity-object étale sections. -/
  toSchemeTopIso : ∀ n : ℕ,
    ((toScheme (Over.mk σA)).obj (tildeB n)).val.obj
        (Opposite.op (⊤ : Opens (Over.mk σA).left)) ≅
      (tildeB n).val.obj (Opposite.op (smallEtaleSite.id (Over.mk σA)))
  /-- Negative-degree pieces of the integer-graded pullback algebra vanish. -/
  negativeDegreeIsZero : ∀ n : ℤ, n < 0 → IsZero (𝓑 n)
  /-- Degreewise identification of the chosen family with the module pullback of the affine
  model. -/
  pullbackIso : ∀ n : ℕ, (pullback f).obj (tildeB n) ≅ 𝓑 n
  /-- Canonical homogeneous elements as maps into compatible sections. -/
  homogeneousSection : ∀ n : ℕ, 𝒜 n → (𝓑 n).sections
  /-- Homogeneous sections are additive on every étale object. -/
  homogeneousSection_add : ∀ (n : ℕ) (a b : 𝒜 n) (V : (smallEtaleSite X)ᵒᵖ),
    (homogeneousSection n (a + b)).1 V =
      (homogeneousSection n a).1 V + (homogeneousSection n b).1 V
  /-- A homogeneous section is the affine tilde section transported through `tildeIso`,
  `toScheme`, and `pullbackIso`. -/
  homogeneousSection_eq : ∀ (n : ℕ) (b : 𝒜 n),
    homogeneousSection n b =
      sectionsMap (pullbackIso n).hom
        (sectionsPullback f (tildeB n)
          (tildeBSectionFromAffine 𝒜 σA tildeB tildeIso toSchemeTopIso n b))
  /-- The homogeneous unit is the unit section of the graded algebra. -/
  homogeneousSection_one :
    homogeneousSection 0 (@GradedMonoid.GOne.one ℕ (fun n ↦ 𝒜 n) _ _) =
      (𝓑 0).val.sectionsMk one (fun _ _ i ↦ map_one i)
  /-- The canonical homogeneous sections preserve graded multiplication. -/
  homogeneousSection_mul : ∀ (m n : ℕ) (a : 𝒜 m) (b : 𝒜 n) (U : (smallEtaleSite X)ᵒᵖ),
    (homogeneousSection (m + n)
        (@GradedMonoid.GMul.mul ℕ (fun n ↦ 𝒜 n) _ _ m n a b)).1 U =
      mul U (m : ℤ) (n : ℤ) ((homogeneousSection m a).1 U) ((homogeneousSection n b).1 U)

namespace Comparison

/-- Constructs a comparison from an affine model, degree identifications, pullback identifications,
graded algebra data, and the canonical homogeneous-section transport. -/
def ofComponents {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    (𝒜 : ℕ → Submodule A B) [GradedAlgebra 𝒜] {X : AlgebraicSpace S}
    (σA : Spec (CommRingCat.of A) ⟶ S) (f : X ⟶ ofOver (Over.mk σA))
    (𝓑 : ℤ → X.Modules)
    (one : ∀ U : (smallEtaleSite X)ᵒᵖ, (𝓑 0).val.obj U)
    (mul : ∀ (U : (smallEtaleSite X)ᵒᵖ) (n m : ℤ),
      (𝓑 n).val.obj U → (𝓑 m).val.obj U → (𝓑 (n + m)).val.obj U)
    (map_one : ∀ {U V : (smallEtaleSite X)ᵒᵖ} (i : U ⟶ V),
      ((𝓑 0).val.map i).hom (one U) = one V)
    (map_mul : ∀ {U V : (smallEtaleSite X)ᵒᵖ} (i : U ⟶ V) (n m : ℤ)
      (a : (𝓑 n).val.obj U) (b : (𝓑 m).val.obj U),
      ((𝓑 (n + m)).val.map i).hom (mul U n m a b) =
        mul V n m (((𝓑 n).val.map i).hom a) (((𝓑 m).val.map i).hom b))
    (mul_add : ∀ (U : (smallEtaleSite X)ᵒᵖ) (n m : ℤ)
      (a₁ a₂ : (𝓑 n).val.obj U) (b : (𝓑 m).val.obj U),
      mul U n m (a₁ + a₂) b = mul U n m a₁ b + mul U n m a₂ b)
    (add_mul : ∀ (U : (smallEtaleSite X)ᵒᵖ) (n m : ℤ)
      (a : (𝓑 n).val.obj U) (b₁ b₂ : (𝓑 m).val.obj U),
      mul U n m a (b₁ + b₂) = mul U n m a b₁ + mul U n m a b₂)
    (smul_mul : ∀ (U : (smallEtaleSite X)ᵒᵖ) (n m : ℤ)
      (r : (structureSheaf X).obj.obj U) (a : (𝓑 n).val.obj U) (b : (𝓑 m).val.obj U),
      mul U n m (r • a) b = r • mul U n m a b)
    (mul_smul : ∀ (U : (smallEtaleSite X)ᵒᵖ) (n m : ℤ)
      (r : (structureSheaf X).obj.obj U) (a : (𝓑 n).val.obj U) (b : (𝓑 m).val.obj U),
      mul U n m a (r • b) = r • mul U n m a b)
    (mul_assoc : ∀ (U : (smallEtaleSite X)ᵒᵖ) (i j k : ℤ)
      (a : (𝓑 i).val.obj U) (b : (𝓑 j).val.obj U) (c : (𝓑 k).val.obj U),
      HEq (mul U (i + j) k (mul U i j a b) c) (mul U i (j + k) a (mul U j k b c)))
    (one_mul : ∀ (U : (smallEtaleSite X)ᵒᵖ) (n : ℤ) (a : (𝓑 n).val.obj U),
      HEq (mul U 0 n (one U) a) a)
    (mul_one : ∀ (U : (smallEtaleSite X)ᵒᵖ) (n : ℤ) (a : (𝓑 n).val.obj U),
      HEq (mul U n 0 a (one U)) a)
    (tildeB : ℕ → (ofOver (Over.mk σA)).Modules)
    (tildeIso : ∀ n : ℕ,
      (toScheme (Over.mk σA)).obj (tildeB n) ≅
        (tilde.functor (CommRingCat.of A)).obj (ModuleCat.of (CommRingCat.of A) (𝒜 n)))
    (toSchemeTopIso : ∀ n : ℕ,
      ((toScheme (Over.mk σA)).obj (tildeB n)).val.obj
          (Opposite.op (⊤ : Opens (Over.mk σA).left)) ≅
        (tildeB n).val.obj (Opposite.op (smallEtaleSite.id (Over.mk σA))))
    (negativeDegreeIsZero : ∀ n : ℤ, n < 0 → IsZero (𝓑 n))
    (pullbackIso : ∀ n : ℕ, (pullback f).obj (tildeB n) ≅ 𝓑 n)
    (homogeneousSection : ∀ n : ℕ, 𝒜 n → (𝓑 n).sections)
    (homogeneousSection_add : ∀ (n : ℕ) (a b : 𝒜 n) (V : (smallEtaleSite X)ᵒᵖ),
      (homogeneousSection n (a + b)).1 V =
        (homogeneousSection n a).1 V + (homogeneousSection n b).1 V)
    (homogeneousSection_eq : ∀ (n : ℕ) (b : 𝒜 n),
      homogeneousSection n b =
        sectionsMap (pullbackIso n).hom
          (sectionsPullback f (tildeB n)
            (tildeBSectionFromAffine 𝒜 σA tildeB tildeIso toSchemeTopIso n b)))
    (homogeneousSection_one :
      homogeneousSection 0 (@GradedMonoid.GOne.one ℕ (fun n ↦ 𝒜 n) _ _) =
        (𝓑 0).val.sectionsMk one (fun _ _ i ↦ map_one i))
    (homogeneousSection_mul : ∀ (m n : ℕ) (a : 𝒜 m) (b : 𝒜 n) (U : (smallEtaleSite X)ᵒᵖ),
      (homogeneousSection (m + n)
          (@GradedMonoid.GMul.mul ℕ (fun n ↦ 𝒜 n) _ _ m n a b)).1 U =
        mul U (m : ℤ) (n : ℤ) ((homogeneousSection m a).1 U) ((homogeneousSection n b).1 U)) :
    Comparison 𝒜 σA f 𝓑 :=
  { one := one
    mul := mul
    map_one := map_one
    map_mul := map_mul
    mul_add := mul_add
    add_mul := add_mul
    smul_mul := smul_mul
    mul_smul := mul_smul
    mul_assoc := mul_assoc
    one_mul := one_mul
    mul_one := mul_one
    tildeB := tildeB
    tildeIso := tildeIso
    toSchemeTopIso := toSchemeTopIso
    negativeDegreeIsZero := negativeDegreeIsZero
    pullbackIso := pullbackIso
    homogeneousSection := homogeneousSection
    homogeneousSection_add := homogeneousSection_add
    homogeneousSection_eq := homogeneousSection_eq
    homogeneousSection_one := homogeneousSection_one
    homogeneousSection_mul := homogeneousSection_mul }

/-- The degreewise pullback identifications underlying an affine-tilde comparison. -/
def toPullbackIso {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    {𝒜 : ℕ → Submodule A B} [GradedAlgebra 𝒜] {X : AlgebraicSpace S}
    {σA : Spec (CommRingCat.of A) ⟶ S} {f : X ⟶ ofOver (Over.mk σA)}
    {𝓑 : ℤ → X.Modules} (pullbackData : Comparison 𝒜 σA f 𝓑) :
    ∀ n : ℕ, (pullback f).obj (pullbackData.tildeB n) ≅ 𝓑 n :=
  pullbackData.pullbackIso

/-- The unit morphism `𝒪_X ⟶ 𝓑 0` classified by the homogeneous unit section. -/
def oneHom {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    {𝒜 : ℕ → Submodule A B} [GradedAlgebra 𝒜] {X : AlgebraicSpace S}
    {σA : Spec (CommRingCat.of A) ⟶ S} {f : X ⟶ ofOver (Over.mk σA)}
    {𝓑 : ℤ → X.Modules} (pullbackData : Comparison 𝒜 σA f 𝓑) :
    unit (structureSheaf X) ⟶ 𝓑 0 :=
  (unitHomEquiv (𝓑 0)).symm
    (pullbackData.homogeneousSection 0 (@GradedMonoid.GOne.one ℕ (fun n ↦ 𝒜 n) _ _))

/-- The pullback-tilde comparison simultaneously specifies negative-degree vanishing, its
canonical homogeneous sections, their unit and multiplication laws, and the degreewise
pullback identifications. -/
theorem spec {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    (𝒜 : ℕ → Submodule A B) [GradedAlgebra 𝒜] {X : AlgebraicSpace S}
    (σA : Spec (CommRingCat.of A) ⟶ S) (f : X ⟶ ofOver (Over.mk σA))
    {𝓑 : ℤ → X.Modules} (pullbackData : Comparison 𝒜 σA f 𝓑) :
    (∀ n : ℤ, n < 0 → IsZero (𝓑 n)) ∧
    (∀ n : ℕ, pullbackData.toPullbackIso n = pullbackData.pullbackIso n) ∧
    (∀ (n : ℕ) (b : 𝒜 n),
      pullbackData.homogeneousSection n b =
        sectionsMap (pullbackData.pullbackIso n).hom
          (sectionsPullback f (pullbackData.tildeB n)
            (tildeBSectionFromAffine 𝒜 σA pullbackData.tildeB pullbackData.tildeIso
              pullbackData.toSchemeTopIso n b))) ∧
    (pullbackData.homogeneousSection 0
        (@GradedMonoid.GOne.one ℕ (fun n ↦ 𝒜 n) _ _) =
      OXGradedAlgebra.oneSection pullbackData.toOXGradedAlgebra) ∧
    (∀ (m n : ℕ) (a : 𝒜 m) (b : 𝒜 n) (U : (smallEtaleSite X)ᵒᵖ),
      (pullbackData.homogeneousSection (m + n)
          (@GradedMonoid.GMul.mul ℕ (fun n ↦ 𝒜 n) _ _ m n a b)).1 U =
        pullbackData.mul U (m : ℤ) (n : ℤ)
          ((pullbackData.homogeneousSection m a).1 U)
          ((pullbackData.homogeneousSection n b).1 U)) ∧
    (∀ {U V : (smallEtaleSite X)ᵒᵖ} (i : U ⟶ V),
      ((𝓑 0).val.map i).hom (pullbackData.one U) = pullbackData.one V) ∧
    (∀ {U V : (smallEtaleSite X)ᵒᵖ} (i : U ⟶ V) (n m : ℤ)
      (a : (𝓑 n).val.obj U) (b : (𝓑 m).val.obj U),
      ((𝓑 (n + m)).val.map i).hom (pullbackData.mul U n m a b) =
        pullbackData.mul V n m (((𝓑 n).val.map i).hom a) (((𝓑 m).val.map i).hom b)) :=
  sorry

end Comparison

end PullbackTilde

end AlgebraicGeometry.AlgebraicSpace.Modules
