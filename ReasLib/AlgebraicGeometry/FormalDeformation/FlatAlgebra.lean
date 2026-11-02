/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.CategoryTheory.FiberedCategory.Fiber
public import ReasLib.AlgebraicGeometry.FormalDeformation.ArtinianLocal.Residue
public import ReasLib.CategoryTheory.Fibered.InGroupoids.Basic

/-!
# Category of flat algebras over `ArtinianLocalAlgCat`

Objects are pairs `(A, P)` with `A` in `ArtinianLocalAlgCat` and `P` a
commutative flat `A`-algebra. Morphisms are pairs `(f, g)` with `g` an
`f`-linear ring map inducing the canonical base-change isomorphism.
-/

@[expose] public section

open CategoryTheory Functor
open scoped TensorProduct

universe u

variable (Λ k : Type u) [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

/-- Flat commutative algebras over varying Artinian local bases. -/
def FlatAlgebraCat : Type (u + 1) :=
  Σ A : ArtinianLocalAlgCat Λ k, { P : CommAlgCat.{u} A.carrier // Module.Flat A.carrier P }

namespace FlatAlgebraCat

variable {Λ k}

/-- The Artinian local base of a flat algebra. -/
def base (X : FlatAlgebraCat Λ k) : ArtinianLocalAlgCat Λ k := X.1

/-- The carrier of a flat algebra over an Artinian local base. -/
def algebra (X : FlatAlgebraCat Λ k) : Type u := X.2.1.carrier

/-- The categorical carrier has its stored commutative ring structure. -/
instance commRing (X : FlatAlgebraCat Λ k) : CommRing X.algebra :=
  X.2.1.commRing

/-- The categorical carrier has its stored algebra structure over the base. -/
instance isAlgebra (X : FlatAlgebraCat Λ k) : Algebra X.base.carrier X.algebra :=
  X.2.1.algebra

/-- The categorical carrier is flat over its stored base. -/
instance isFlat (X : FlatAlgebraCat Λ k) : Module.Flat X.base.carrier X.algebra :=
  X.2.2

/-- Pair an Artinian local algebra with a flat commutative algebra over it. -/
def of (A : ArtinianLocalAlgCat Λ k) (P : Type u) [CommRing P] [isAlgebra : Algebra A.carrier P]
    [isFlat : Module.Flat A.carrier P] : FlatAlgebraCat Λ k :=
  ⟨A, CommAlgCat.of A.carrier P, inferInstance⟩

/-- A flat-algebra object is flat over its stored base. -/
theorem spec (X : FlatAlgebraCat Λ k) : Module.Flat X.base.carrier X.algebra :=
  X.isFlat

/-- The `B`-algebra structure on `A` along a morphism `f : B ⟶ A` in `C_Λ`. -/
abbrev algebraAlong {Q P : FlatAlgebraCat Λ k} (f : Q.base ⟶ P.base) :
    Algebra Q.base.carrier P.base.carrier :=
  Algebra.compHom P.base.carrier f.hom.toRingHom

/-- The `B`-algebra structure on `P` along a morphism `f : B ⟶ A` in `C_Λ`. -/
abbrev compAlgebraAlong {Q P : FlatAlgebraCat Λ k} (f : Q.base ⟶ P.base) :
    Algebra Q.base.carrier P.algebra :=
  Algebra.compHom P.algebra f.hom.toRingHom

/-- Restriction of scalars along `f` acts by the underlying ring map of `f`. -/
theorem algebraAlong_algebraMap {Q P : FlatAlgebraCat Λ k} (f : Q.base ⟶ P.base) :
    (algebraAlong f).algebraMap = f.hom.toRingHom := rfl

/-- The base-change carrier `A ⊗[B] Q` along `f : B ⟶ A`. -/
def tensorAlong {Q P : FlatAlgebraCat Λ k} (f : Q.base ⟶ P.base) : Type u :=
  -- Local instance justification (noncanonical choice): the `B`-algebra structure on `A` is determined by the morphism `f` and cannot be a global instance.
  letI := algebraAlong f
  P.base.carrier ⊗[Q.base.carrier] Q.algebra

/-- Pure tensors in the base-change carrier along `f`. -/
def tmulAlong {Q P : FlatAlgebraCat Λ k} (f : Q.base ⟶ P.base)
    (a : P.base.carrier) (q : Q.algebra) : tensorAlong f :=
  -- Local instance justification (noncanonical choice): the `B`-algebra structure on `A` is determined by the morphism `f` and cannot be a global instance.
  letI := algebraAlong f
  a ⊗ₜ[Q.base.carrier] q

/-- The canonical `A`-algebra map `A ⊗[B, f] Q → P` induced by an `f`-linear ring map. -/
def canonicalTensorMap {Q P : FlatAlgebraCat Λ k} (f : Q.base ⟶ P.base)
    (g : Q.algebra →+* P.algebra)
    (h_commutes :
      g.comp (algebraMap Q.base.carrier Q.algebra) =
        (algebraMap P.base.carrier P.algebra).comp f.hom.toRingHom) :
    tensorAlong f → P.algebra :=
  -- Local instance justification (noncanonical choice): the `B`-algebra structure on `A` is determined by the morphism `f` and cannot be a global instance.
  letI := algebraAlong f
  -- Local instance justification (noncanonical choice): the `B`-algebra structure on `P` is determined by the morphism `f` and cannot be a global instance.
  letI := compAlgebraAlong f
  -- Local instance justification (noncanonical choice): the scalar tower `B → A → P` is determined by the morphism `f` and cannot be a global instance.
  letI : IsScalarTower Q.base.carrier P.base.carrier P.algebra :=
    IsScalarTower.of_algebraMap_eq' rfl
  fun x ↦
    AlgHom.liftEquiv Q.base.carrier P.base.carrier Q.algebra P.algebra
      { g with commutes' := fun r ↦ RingHom.ext_iff.mp h_commutes r } x

/-- The canonical tensor map sends `a ⊗ q` to `a • g q`. -/
theorem canonicalTensorMap_tmul {Q P : FlatAlgebraCat Λ k} (f : Q.base ⟶ P.base)
    (g : Q.algebra →+* P.algebra)
    (h_commutes :
      g.comp (algebraMap Q.base.carrier Q.algebra) =
        (algebraMap P.base.carrier P.algebra).comp f.hom.toRingHom)
    (a : P.base.carrier) (q : Q.algebra) :
    canonicalTensorMap f g h_commutes (tmulAlong f a q) = a • g q := by
  rfl

/-- A base arrow and a scalar-compatible ring map with bijective canonical tensor lift. -/
def Hom (Q P : FlatAlgebraCat Λ k) : Type u :=
  Σ baseHom : Q.base ⟶ P.base, Σ toRingHom : Q.algebra →+* P.algebra,
    { commutes :
        toRingHom.comp (algebraMap Q.base.carrier Q.algebra) =
          (algebraMap P.base.carrier P.algebra).comp baseHom.hom.toRingHom //
      Function.Bijective (canonicalTensorMap baseHom toRingHom commutes) }

namespace Hom

/-- The base morphism of a flat-algebra morphism. -/
def baseHom {Q P : FlatAlgebraCat Λ k} (f : Hom Q P) : Q.base ⟶ P.base :=
  f.1

/-- The underlying ring homomorphism of a flat-algebra morphism. -/
def toRingHom {Q P : FlatAlgebraCat Λ k} (f : Hom Q P) : Q.algebra →+* P.algebra :=
  f.2.1

/-- The ring map of a flat-algebra morphism commutes with its base map. -/
theorem commutes {Q P : FlatAlgebraCat Λ k} (f : Hom Q P) :
    f.toRingHom.comp (algebraMap Q.base.carrier Q.algebra) =
      (algebraMap P.base.carrier P.algebra).comp f.baseHom.hom.toRingHom :=
  f.2.2.1

/-- The canonical tensor lift of a flat-algebra morphism is bijective. -/
theorem isIso_tensor {Q P : FlatAlgebraCat Λ k} (f : Hom Q P) :
    Function.Bijective (canonicalTensorMap f.baseHom f.toRingHom f.commutes) :=
  f.2.2.2

/-- Package a base map and a scalar-compatible ring map inducing a base-change isomorphism. -/
def of {Q P : FlatAlgebraCat Λ k} (baseHom : Q.base ⟶ P.base)
    (toRingHom : Q.algebra →+* P.algebra)
    (commutes :
      toRingHom.comp (algebraMap Q.base.carrier Q.algebra) =
        (algebraMap P.base.carrier P.algebra).comp baseHom.hom.toRingHom)
    (isIso_tensor : Function.Bijective (canonicalTensorMap baseHom toRingHom commutes)) :
    Hom Q P :=
  ⟨baseHom, toRingHom, commutes, isIso_tensor⟩

/-- Identity base and ring maps commute with the algebra structure map. -/
theorem id_commutes (P : FlatAlgebraCat Λ k) :
    (RingHom.id P.algebra).comp (algebraMap P.base.carrier P.algebra) =
      (algebraMap P.base.carrier P.algebra).comp (𝟙 P.base : P.base ⟶ P.base).hom.toRingHom := by
  rfl

/-- The canonical tensor lift of identity base and ring maps is bijective. -/
theorem id_isIsoTensor (P : FlatAlgebraCat Λ k) :
    Function.Bijective
      (canonicalTensorMap (𝟙 P.base) (RingHom.id P.algebra) (id_commutes P)) := by
  change Function.Bijective (TensorProduct.lid P.base.carrier P.algebra)
  exact (TensorProduct.lid P.base.carrier P.algebra).bijective

/-- Composite scalar-compatible ring maps commute with the composite base map. -/
theorem comp_commutes {Q P R : FlatAlgebraCat Λ k} (f : Hom Q P) (g : Hom P R) :
    (g.toRingHom.comp f.toRingHom).comp (algebraMap Q.base.carrier Q.algebra) =
      (algebraMap R.base.carrier R.algebra).comp
        (f.baseHom ≫ g.baseHom).hom.toRingHom := by
  rw [RingHom.comp_assoc, f.commutes, ← RingHom.comp_assoc, g.commutes,
    RingHom.comp_assoc]
  rfl

/-- The canonical tensor lift of a composite of base-change isomorphisms is bijective. -/
theorem comp_isIsoTensor {Q P R : FlatAlgebraCat Λ k} (f : Hom Q P) (g : Hom P R) :
    Function.Bijective (canonicalTensorMap (f.baseHom ≫ g.baseHom)
      (g.toRingHom.comp f.toRingHom) (comp_commutes f g)) := by
  letI := algebraAlong f.baseHom
  letI := compAlgebraAlong f.baseHom
  letI : IsScalarTower Q.base.carrier P.base.carrier P.algebra :=
    IsScalarTower.of_algebraMap_eq' rfl
  let fMap := AlgHom.liftEquiv Q.base.carrier P.base.carrier Q.algebra P.algebra
    { f.toRingHom with commutes' := fun r ↦ RingHom.ext_iff.mp f.commutes r }
  let e := LinearEquiv.ofBijective fMap.toLinearMap f.isIso_tensor
  letI := algebraAlong g.baseHom
  letI := compAlgebraAlong g.baseHom
  letI : IsScalarTower P.base.carrier R.base.carrier R.algebra :=
    IsScalarTower.of_algebraMap_eq' rfl
  letI := algebraAlong (f.baseHom ≫ g.baseHom)
  letI : IsScalarTower Q.base.carrier P.base.carrier R.base.carrier :=
    IsScalarTower.of_algebraMap_eq' rfl
  let gMap := AlgHom.liftEquiv P.base.carrier R.base.carrier P.algebra R.algebra
    { g.toRingHom with commutes' := fun r ↦ RingHom.ext_iff.mp g.commutes r }
  letI := compAlgebraAlong (f.baseHom ≫ g.baseHom)
  letI : IsScalarTower Q.base.carrier R.base.carrier R.algebra :=
    IsScalarTower.of_algebraMap_eq' rfl
  let cancel := TensorProduct.AlgebraTensorModule.cancelBaseChange
    Q.base.carrier P.base.carrier R.base.carrier R.base.carrier Q.algebra
  let e' := e.baseChange P.base.carrier R.base.carrier
  have h : canonicalTensorMap (f.baseHom ≫ g.baseHom)
      (g.toRingHom.comp f.toRingHom) (comp_commutes f g) =
      gMap ∘ e' ∘ cancel.symm := by
    funext x
    change (AlgHom.liftEquiv Q.base.carrier R.base.carrier Q.algebra R.algebra
      { g.toRingHom.comp f.toRingHom with
        commutes' := fun r ↦ RingHom.ext_iff.mp (comp_commutes f g) r }) x = _
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a q =>
      simp [cancel, e', e, fMap, gMap]
    | add x y hx hy =>
      simpa only [_root_.map_add, Function.comp_apply] using congrArg₂ (· + ·) hx hy
  rw [h]
  exact g.isIso_tensor.comp (e'.bijective.comp cancel.symm.bijective)

/-- The identity morphism uses identity base and ring maps. -/
def id (P : FlatAlgebraCat Λ k) : Hom P P :=
  of (𝟙 P.base) (RingHom.id P.algebra) (id_commutes P) (id_isIsoTensor P)

/-- Composition uses the composite base and ring maps. -/
def comp {Q P R : FlatAlgebraCat Λ k} (f : Hom Q P) (g : Hom P R) : Hom Q R :=
  of (f.baseHom ≫ g.baseHom) (g.toRingHom.comp f.toRingHom)
    (comp_commutes f g) (comp_isIsoTensor f g)

/-- A morphism is an `f`-linear ring map whose canonical tensor lift is bijective. -/
theorem spec {Q P : FlatAlgebraCat Λ k} (f : Hom Q P) :
    f.toRingHom.comp (algebraMap Q.base.carrier Q.algebra) =
        (algebraMap P.base.carrier P.algebra).comp f.baseHom.hom.toRingHom ∧
      Function.Bijective (canonicalTensorMap f.baseHom f.toRingHom f.commutes) :=
  ⟨f.commutes, f.isIso_tensor⟩

/-- The identity morphism has identity base arrow. -/
theorem id_baseHom (P : FlatAlgebraCat Λ k) : (id P).baseHom = 𝟙 P.base := rfl

/-- Composition of morphisms has composed base arrows. -/
theorem comp_baseHom {Q P R : FlatAlgebraCat Λ k} (f : Hom Q P) (g : Hom P R) :
    (comp f g).baseHom = f.baseHom ≫ g.baseHom := rfl

/-- The identity is a left identity for flat-algebra morphism composition. -/
theorem id_comp {Q P : FlatAlgebraCat Λ k} (f : Hom Q P) : comp (id Q) f = f := by
  rcases f with ⟨fb, fr, fc⟩
  rfl

/-- The identity is a right identity for flat-algebra morphism composition. -/
theorem comp_id {Q P : FlatAlgebraCat Λ k} (f : Hom Q P) : comp f (id P) = f := by
  rcases f with ⟨fb, fr, fc⟩
  rfl

/-- Composition of flat-algebra morphisms is associative. -/
theorem assoc {Q P R S : FlatAlgebraCat Λ k} (f : Hom Q P) (g : Hom P R)
    (h : Hom R S) : comp (comp f g) h = comp f (comp g h) := by
  rfl

end Hom

/-- Category of pairs `(A, P)` with cartesian algebra maps. -/
instance category : Category.{u} (FlatAlgebraCat Λ k) where
  Hom := Hom
  id := Hom.id
  comp f g := Hom.comp f g
  id_comp := Hom.id_comp
  comp_id := Hom.comp_id
  assoc := Hom.assoc

/-- The projection of a flat algebra to its Artinian local base. -/
def forget : FlatAlgebraCat Λ k ⥤ ArtinianLocalAlgCat Λ k where
  obj X := X.base
  map f := f.baseHom
  map_id := Hom.id_baseHom
  map_comp := Hom.comp_baseHom

/-- The forgetful functor evaluates to the stored base algebra. -/
theorem forget_obj (X : FlatAlgebraCat Λ k) : forget.obj X = X.base := rfl

/-- The forgetful functor sends a morphism to its base arrow. -/
theorem forget_map {Q P : FlatAlgebraCat Λ k} (f : Q ⟶ P) : forget.map f = f.baseHom := rfl

/-- The projection of flat algebras to their bases is cofibered in groupoids. -/
instance instIsFiberedInGroupoids_forget :
    IsFibered.InGroupoids
      (forget : FlatAlgebraCat Λ k ⥤ ArtinianLocalAlgCat Λ k).op := sorry

variable (Λ k)

/-- A commutative residue-field algebra determines a flat algebra over the residue base. -/
def ofResidue (P : Type u) [CommRing P] [Algebra k P] : FlatAlgebraCat Λ k :=
  of (ArtinianLocalAlgCat.residue Λ k) P
    (isAlgebra := inferInstanceAs (Algebra k P))
    (isFlat := inferInstanceAs (Module.Flat k P))

/-- The base of a residue-field algebra is the residue object. -/
theorem ofResidue_base (P : Type u) [CommRing P] [Algebra k P] :
    (ofResidue Λ k P).base = ArtinianLocalAlgCat.residue Λ k := rfl

/-- A commutative residue-field algebra as an object of the strict residue fiber. -/
def residueObj (P : Type u) [CommRing P] [Algebra k P] :
    forget.Fiber (ArtinianLocalAlgCat.residue Λ k) :=
  Fiber.mk (rfl : forget.obj (ofResidue Λ k P) = ArtinianLocalAlgCat.residue Λ k)

/-- The residue-fibre object is included as `ofResidue P`. -/
theorem residueObj_fiberInclusion (P : Type u) [CommRing P] [Algebra k P] :
    Fiber.fiberInclusion.obj (residueObj Λ k P) = ofResidue Λ k P := rfl

/-- The deformation category of a residue-field algebra is the slice over its residue object. -/
abbrev deformationCategory (P : Type u) [CommRing P] [Algebra k P] :=
  Over (Fiber.fiberInclusion.obj (residueObj Λ k P))

/-- The deformation category is the slice over the included residue-fiber object. -/
theorem deformationCategory_spec (P : Type u) [CommRing P] [Algebra k P] :
    deformationCategory Λ k P = Over (Fiber.fiberInclusion.obj (residueObj Λ k P)) := rfl

end FlatAlgebraCat
