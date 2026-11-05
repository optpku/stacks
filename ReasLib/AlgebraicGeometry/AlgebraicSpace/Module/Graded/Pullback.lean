/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.AlgebraicGeometry.Spec
public import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects
public import Mathlib.RingTheory.GradedAlgebra.Basic
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.TopSections
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Pullback.Sections
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.ToSpec
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSheafSpace

/-! # Graded algebras pulled back from affine tilde algebras -/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open SheafOfModules

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

variable {S : Scheme.{u}}

namespace PullbackTilde

/-- The étale chart selected by `toScheme` at the top open. -/
def toSchemeTopObject (U : Over S) : smallEtaleSite (ofOver U) :=
  (schemeEtaleRingedHom U).base.obj
    ((smallEtaleToOpensRingedHom U.left).base.obj (⊤ : U.left.Opens))
/-- The top-open chart is canonically isomorphic to the identity chart, using
`Scheme.topIso` in both directions. -/
def toSchemeTopObjectIso (U : Over S) : toSchemeTopObject U ≅ smallEtaleSite.id U :=
  MorphismProperty.CostructuredArrow.isoMk
    (Over.isoMk U.left.topIso (by
      change (⊤ : U.left.Opens).ι ≫ U.hom = (⊤ : U.left.Opens).ι ≫ U.hom
      rfl)) trivial trivial (by
      change (ofOverFunctor S).map _ ≫ 𝟙 _ = _
      rw [Category.comp_id]
      rfl)
/-- Restriction of an étale module along the canonical top-open chart isomorphism. -/
def toSchemeTopEtaleSectionsIso (U : Over S) (F : (ofOver U).Modules) :
    F.val.obj (op (toSchemeTopObject U)) ≃+
      F.val.obj (op (smallEtaleSite.id U)) :=
  (F.val.presheaf.mapIso (toSchemeTopObjectIso U).op).symm.addCommGroupIsoToAddEquiv

/-- Canonical identification of Zariski-top sections with identity-chart étale sections.
Both maps are restrictions along the explicit top-open chart isomorphism. -/
def toSchemeTopSectionsIso (U : Over S) (F : (ofOver U).Modules) :
    ((toScheme U).obj F).val.obj (op (⊤ : U.left.Opens)) ≃+
      F.val.obj (op (smallEtaleSite.id U)) :=
  (show ((toScheme U).obj F).val.obj (op (⊤ : U.left.Opens)) ≃+
      F.val.obj (op (toSchemeTopObject U)) from AddEquiv.refl _).trans
    (toSchemeTopEtaleSectionsIso U F)

/-- The top-section comparison is the specified restriction, with no automorphism choice. -/
theorem toSchemeTopSectionsIso_apply (U : Over S) (F : (ofOver U).Modules)
    (s : ((toScheme U).obj F).val.obj (op (⊤ : U.left.Opens))) :
    toSchemeTopSectionsIso U F s = F.val.map (toSchemeTopObjectIso U).inv.op s := rfl

/-- The canonical top-section comparison commutes with module morphisms. -/
theorem toSchemeTopSectionsIso_naturality (U : Over S) {F G : (ofOver U).Modules}
    (φ : F ⟶ G) (s : ((toScheme U).obj F).val.obj (op (⊤ : U.left.Opens))) :
    toSchemeTopSectionsIso U G (((toScheme U).map φ).val.app (op ⊤) s) =
      φ.val.app (op (smallEtaleSite.id U)) (toSchemeTopSectionsIso U F s) :=
  (PresheafOfModules.naturality_apply φ.val (toSchemeTopObjectIso U).inv.op s).symm

/-- Scalar compatibility uses the actual restriction of the structure sheaf along the
top-open chart isomorphism. -/
theorem toSchemeTopEtaleSectionsIso_map_smul (U : Over S) (F : (ofOver U).Modules)
    (r : (structureSheaf (ofOver U)).obj.obj (op (toSchemeTopObject U)))
    (s : F.val.obj (op (toSchemeTopObject U))) :
    toSchemeTopEtaleSectionsIso U F (r • s) =
      (structureSheaf (ofOver U)).obj.map (toSchemeTopObjectIso U).inv.op r •
        toSchemeTopEtaleSectionsIso U F s :=
  F.val.map_smul (toSchemeTopObjectIso U).inv.op r s

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
  rfl

/-- The compatible scheme-module section determined by a homogeneous affine tilde value. -/
def affineTildeCompatibleSection {A : Type u} [CommRing A] {B : Type u} [CommRing B]
    [Algebra A B] (𝒜 : ℕ → Submodule A B) (n : ℕ) (b : 𝒜 n) :
    ((tilde.functor (CommRingCat.of A)).obj (ModuleCat.of (CommRingCat.of A) (𝒜 n))).sections :=
  RingedSpace.sectionFromTop
    ((tilde.functor (CommRingCat.of A)).obj (ModuleCat.of (CommRingCat.of A) (𝒜 n)))
    (affineTildeSection 𝒜 n b)

/-- A commutative graded `𝒪_X`-algebra given degreewise as modules on an algebraic space. -/
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
  /-- Multiplication is commutative, with the canonical change of degree. -/
  mul_comm : ∀ (U : (smallEtaleSite X)ᵒᵖ) (i j : ℤ)
    (a : (𝓑 i).val.obj U) (b : (𝓑 j).val.obj U),
    HEq (mul U i j a b) (mul U j i b a)
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

/-- Constructs a commutative graded algebra from local operations and their laws. -/
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
    (mul_comm : ∀ (U : (smallEtaleSite X)ᵒᵖ) (i j : ℤ)
      (a : (𝓑 i).val.obj U) (b : (𝓑 j).val.obj U),
      HEq (mul U i j a b) (mul U j i b a))
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
    mul_comm := mul_comm
    mul_assoc := mul_assoc
    one_mul := one_mul
    mul_one := mul_one }

/-- The compatible global unit section of a graded algebra. -/
def oneSection {X : AlgebraicSpace S} {𝓑 : ℤ → X.Modules} (alg : OXGradedAlgebra 𝓑) :
    (𝓑 0).sections :=
  (𝓑 0).val.sectionsMk alg.one fun _ _ i ↦ alg.map_one i

/-- The product of compatible sections, induced by the local sheaf multiplication. -/
def mulSection {X : AlgebraicSpace S} {𝓑 : ℤ → X.Modules} (alg : OXGradedAlgebra 𝓑)
    (n m : ℤ) (a : (𝓑 n).sections) (b : (𝓑 m).sections) : (𝓑 (n + m)).sections :=
  (𝓑 (n + m)).val.sectionsMk (fun U ↦ alg.mul U n m (a.1 U) (b.1 U))
    (fun _ _ i ↦ (alg.map_mul i n m (a.1 _) (b.1 _)).trans
      (congrArg₂ (alg.mul _ n m)
        (PresheafOfModules.sections_property a i)
        (PresheafOfModules.sections_property b i)))

/-- Multiplication by a compatible section is a morphism of sheaves of modules. -/
def mulHom {X : AlgebraicSpace S} {𝓑 : ℤ → X.Modules} (alg : OXGradedAlgebra 𝓑)
    (n m : ℤ) (b : (𝓑 m).sections) : 𝓑 n ⟶ 𝓑 (n + m) :=
  ⟨{ app := fun U ↦
      ModuleCat.ofHom
        { toFun := fun a ↦ alg.mul U n m a (b.1 U)
          map_add' := fun a₁ a₂ ↦ alg.mul_add U n m a₁ a₂ (b.1 U)
          map_smul' := fun r a ↦ alg.smul_mul U n m r a (b.1 U) }
     naturality := by
       intro U V i
       ext a
       exact (congrArg (alg.mul V n m (((𝓑 n).val.map i).hom a))
         (PresheafOfModules.sections_property b i).symm).trans
           (alg.map_mul i n m a (b.1 U)).symm }⟩

/-- The sheaf multiplication morphism evaluates to the specified local multiplication. -/
theorem mulHom_apply {X : AlgebraicSpace S} {𝓑 : ℤ → X.Modules} (alg : OXGradedAlgebra 𝓑)
    (n m : ℤ) (b : (𝓑 m).sections) (U : (smallEtaleSite X)ᵒᵖ)
    (a : (𝓑 n).val.obj U) :
    (alg.mulHom n m b).val.app U a = alg.mul U n m a (b.1 U) := rfl

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
  ⟨alg.map_one, alg.map_mul, alg.mul_assoc, alg.one_mul, alg.mul_one⟩

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
    (n : ℕ) (b : 𝒜 n) : (tildeB n).sections :=
  (tildeB n).val.sectionsMk
    (fun V ↦
      ((tildeB n).val.map (smallEtaleSite.homToId (Over.mk σA) V.unop).op)
        ((toSchemeTopSectionsIso (Over.mk σA) (tildeB n))
          ((sectionsMap (tildeIso n).inv (affineTildeCompatibleSection 𝒜 n b)).1
            (Opposite.op (⊤ : Opens (Over.mk σA).left)))))
    (by
      intro U V i
      have unique {W : smallEtaleSite (ofOver (Over.mk σA))}
          (g h : W ⟶ smallEtaleSite.id (Over.mk σA)) : g = h := by
        apply MorphismProperty.CostructuredArrow.Hom.ext
        apply yoneda.map_injective
        have hg : (ofOverFunctor S).map g.left ≫ 𝟙 (ofOver (Over.mk σA)) =
            W.hom ≫ 𝟙 (ofOver (Over.mk σA)) := g.w
        have hh : (ofOverFunctor S).map h.left ≫ 𝟙 (ofOver (Over.mk σA)) =
            W.hom ≫ 𝟙 (ofOver (Over.mk σA)) := h.w
        have hgh : (ofOverFunctor S).map g.left = (ofOverFunctor S).map h.left := by
          exact (Category.comp_id (obj := AlgebraicSpace S) ((ofOverFunctor S).map g.left)).symm.trans
            ((hg.trans hh.symm).trans
              (Category.comp_id (obj := AlgebraicSpace S) ((ofOverFunctor S).map h.left)))
        exact hgh
      rw [← (tildeB n).val.map_comp_apply]
      apply (tildeB n).val.congr_map_apply
      exact congrArg Quiver.Hom.op (unique _ _))

/-- The section determined by the displayed affine model and comparison maps.
This is a transport through supplied data, not a construction of those comparison maps. -/
def transportedHomogeneousSection {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    (𝒜 : ℕ → Submodule A B) {X : AlgebraicSpace S}
    (σA : Spec (CommRingCat.of A) ⟶ S) (f : X ⟶ ofOver (Over.mk σA))
    (𝓑 : ℤ → X.Modules)
    (tildeB : ℕ → (ofOver (Over.mk σA)).Modules)
    (tildeIso : ∀ n : ℕ,
      (toScheme (Over.mk σA)).obj (tildeB n) ≅
        (tilde.functor (CommRingCat.of A)).obj (ModuleCat.of (CommRingCat.of A) (𝒜 n)))
    (pullbackIso : ∀ n : ℕ, (pullback f).obj (tildeB n) ≅ 𝓑 n)
    (n : ℕ) (b : 𝒜 n) : (𝓑 n).sections :=
  sectionsMap (pullbackIso n).hom
    (sectionsPullback f (tildeB n)
      (tildeBSectionFromAffine 𝒜 σA tildeB tildeIso n b))

/-- Assumptions/data facade for a chosen affine-tilde presentation.

The affine models and their comparison maps, negative-degree vanishing, and compatibility
with the target algebra are supplied by the caller. This structure is not a canonical
comparison theorem or a producer from the geometric inputs alone. Homogeneous sections
are determined by transport through these maps, rather than supplied independently.
The top-section comparison is the canonical restriction along `Scheme.topIso`.
A canonical graded affine model and its unit/multiplication coherence remain necessary
to turn this facade into a canonical comparison construction. -/
structure Comparison {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    (𝒜 : ℕ → Submodule A B) [GradedAlgebra 𝒜] {X : AlgebraicSpace S}
    (σA : Spec (CommRingCat.of A) ⟶ S) (f : X ⟶ ofOver (Over.mk σA))
    (𝓑 : ℤ → X.Modules) extends OXGradedAlgebra 𝓑 where
  /-- Quasi-coherent affine models of the nonnegative homogeneous pieces on
  `ofOver (Over.mk σA)`. -/
  tildeB : ℕ → (ofOver (Over.mk σA)).Modules
  /-- Each affine model is quasi-coherent on the small étale site. -/
  tildeBQuasicoherent : ∀ n : ℕ, (tildeB n).IsQuasicoherent
  /-- Degreewise identification of the Zariski restriction of the quasi-coherent affine model
  with the associated sheaf of the homogeneous piece. -/
  tildeIso : ∀ n : ℕ,
    (toScheme (Over.mk σA)).obj (tildeB n) ≅
      (tilde.functor (CommRingCat.of A)).obj (ModuleCat.of (CommRingCat.of A) (𝒜 n))
  /-- Negative-degree pieces of the integer-graded pullback algebra vanish. -/
  negativeDegreeIsZero : ∀ n : ℤ, n < 0 → IsZero (𝓑 n)
  /-- Degreewise identification of the chosen family with the module pullback of the affine
  model. -/
  pullbackIso : ∀ n : ℕ, (pullback f).obj (tildeB n) ≅ 𝓑 n
  /-- Additivity of the section transport, supplied as an assumption. -/
  homogeneousSection_add :
    let sec := transportedHomogeneousSection 𝒜 σA f 𝓑 tildeB tildeIso pullbackIso
    ∀ (n : ℕ) (a b : 𝒜 n) (V : (smallEtaleSite X)ᵒᵖ),
      (sec n (a + b)).1 V = (sec n a).1 V + (sec n b).1 V
  /-- Compatibility of the transported unit with the target unit, supplied as an assumption. -/
  homogeneousSection_one :
    let sec := transportedHomogeneousSection 𝒜 σA f 𝓑 tildeB tildeIso pullbackIso
    sec 0 (@GradedMonoid.GOne.one ℕ (fun n ↦ 𝒜 n) _ _) =
      (𝓑 0).val.sectionsMk one (fun _ _ i ↦ map_one i)
  /-- Compatibility of transport with multiplication, supplied as an assumption. -/
  homogeneousSection_mul :
    let sec := transportedHomogeneousSection 𝒜 σA f 𝓑 tildeB tildeIso pullbackIso
    ∀ (m n : ℕ) (a : 𝒜 m) (b : 𝒜 n) (U : (smallEtaleSite X)ᵒᵖ),
      (sec (m + n) (@GradedMonoid.GMul.mul ℕ (fun n ↦ 𝒜 n) _ _ m n a b)).1 U =
        mul U (m : ℤ) (n : ℤ) ((sec m a).1 U) ((sec n b).1 U)

namespace Comparison

/-- The top-section identification is computed from the actual scheme/site comparison;
it is not an independent choice in an affine-tilde presentation. -/
def toSchemeTopIso {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    {𝒜 : ℕ → Submodule A B} [GradedAlgebra 𝒜] {X : AlgebraicSpace S}
    {σA : Spec (CommRingCat.of A) ⟶ S} {f : X ⟶ ofOver (Over.mk σA)}
    {𝓑 : ℤ → X.Modules} (c : Comparison 𝒜 σA f 𝓑) (n : ℕ) :
    ((toScheme (Over.mk σA)).obj (c.tildeB n)).val.obj
        (Opposite.op (⊤ : Opens (Over.mk σA).left)) ≃+
      (c.tildeB n).val.obj (Opposite.op (smallEtaleSite.id (Over.mk σA))) :=
  toSchemeTopSectionsIso (Over.mk σA) (c.tildeB n)

/-- The homogeneous section is determined by the chosen comparison maps. -/
def homogeneousSection {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    {𝒜 : ℕ → Submodule A B} [GradedAlgebra 𝒜] {X : AlgebraicSpace S}
    {σA : Spec (CommRingCat.of A) ⟶ S} {f : X ⟶ ofOver (Over.mk σA)}
    {𝓑 : ℤ → X.Modules} (c : Comparison 𝒜 σA f 𝓑) (n : ℕ) (b : 𝒜 n) :
    (𝓑 n).sections :=
  transportedHomogeneousSection 𝒜 σA f 𝓑 c.tildeB c.tildeIso c.pullbackIso n b

/-- The section transport formula is a computation rule, not an assumption. -/
theorem homogeneousSection_eq {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    {𝒜 : ℕ → Submodule A B} [GradedAlgebra 𝒜] {X : AlgebraicSpace S}
    {σA : Spec (CommRingCat.of A) ⟶ S} {f : X ⟶ ofOver (Over.mk σA)}
    {𝓑 : ℤ → X.Modules} (c : Comparison 𝒜 σA f 𝓑) (n : ℕ) (b : 𝒜 n) :
    c.homogeneousSection n b =
      sectionsMap (c.pullbackIso n).hom
        (sectionsPullback f (c.tildeB n)
          (tildeBSectionFromAffine 𝒜 σA c.tildeB c.tildeIso n b)) :=
  rfl

/-- The transported homogeneous section is compatible with every restriction. -/
theorem homogeneousSection_map {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    {𝒜 : ℕ → Submodule A B} [GradedAlgebra 𝒜] {X : AlgebraicSpace S}
    {σA : Spec (CommRingCat.of A) ⟶ S} {f : X ⟶ ofOver (Over.mk σA)}
    {𝓑 : ℤ → X.Modules} (c : Comparison 𝒜 σA f 𝓑) (n : ℕ) (b : 𝒜 n)
    {U V : (smallEtaleSite X)ᵒᵖ} (i : U ⟶ V) :
    ((𝓑 n).val.map i).hom ((c.homogeneousSection n b).1 U) =
      (c.homogeneousSection n b).1 V :=
  (c.homogeneousSection n b).property i

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

/-- Collects the supplied assumptions and the proved section computation rule.
This is the specification of a chosen presentation, not a canonical comparison theorem. -/
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
            (tildeBSectionFromAffine 𝒜 σA pullbackData.tildeB pullbackData.tildeIso n b))) ∧
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
  ⟨pullbackData.negativeDegreeIsZero, fun _ ↦ rfl,
    pullbackData.homogeneousSection_eq, pullbackData.homogeneousSection_one,
    pullbackData.homogeneousSection_mul, pullbackData.map_one, pullbackData.map_mul⟩

end Comparison

end PullbackTilde

end AlgebraicGeometry.AlgebraicSpace.Modules
