/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.TensorProduct.Basic
public import stacks_project.Chap90.Definition_90_16_8_Predeformation

/-!
# Category of flat algebras over `ArtinianLocalAlgCat`

Objects are pairs `(A, P)` with `A` in `ArtinianLocalAlgCat` and `P` a
commutative flat `A`-algebra, as in Example 93.8.1. This copy lives over the
residue object of Definition 90.16.8 used by `FlatSchemeCat`, so `Def_X` and
`Def_P` are deformation categories over the same `C_Λ`.
-/

@[expose] public section

open CategoryTheory Functor
open scoped TensorProduct

universe u

variable (Λ k : Type u) [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

/-- An object of the category `F` of pairs `(A, P)` with `A` in `C_Λ` and `P` a
flat commutative `A`-algebra. -/
structure FlatAlgebraCat where
  /-- Underlying object of `ArtinianLocalAlgCat Λ k`. -/
  base : ArtinianLocalAlgCat Λ k
  /-- Underlying commutative algebra over the base. -/
  algebra : Type u
  [commRing : CommRing algebra]
  [isAlgebra : Algebra base.carrier algebra]
  [isFlat : Module.Flat base.carrier algebra]

attribute [instance] FlatAlgebraCat.commRing FlatAlgebraCat.isAlgebra FlatAlgebraCat.isFlat

namespace FlatAlgebraCat

variable {Λ k}

/-- Pair an Artinian local algebra with a flat commutative algebra over it. -/
def of (A : ArtinianLocalAlgCat Λ k) (P : Type u) [CommRing P] [Algebra A.carrier P]
    [Module.Flat A.carrier P] : FlatAlgebraCat Λ k where
  base := A
  algebra := P

/-- An object of `F` is a flat algebra over its stored base in `C_Λ`. -/
theorem spec (X : FlatAlgebraCat Λ k) : Module.Flat X.base.carrier X.algebra := sorry

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
    (algebraAlong f).algebraMap = f.hom.toRingHom := sorry

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
    canonicalTensorMap f g h_commutes (tmulAlong f a q) = a • g q := sorry

/-- A morphism `(f, g) : (B, Q) ⟶ (A, P)` is a morphism `f : B ⟶ A` in `C_Λ` together
with an `f`-linear ring map `g : Q → P` inducing an isomorphism `Q ⊗_{B, f} A ≅ P`. -/
structure Hom (Q P : FlatAlgebraCat Λ k) where
  /-- Underlying morphism of Artinian local algebras. -/
  baseHom : Q.base ⟶ P.base
  /-- Underlying ring homomorphism. -/
  toRingHom : Q.algebra →+* P.algebra
  /-- `f`-linearity as the algebra-map square. -/
  commutes :
    toRingHom.comp (algebraMap Q.base.carrier Q.algebra) =
      (algebraMap P.base.carrier P.algebra).comp baseHom.hom.toRingHom
  /-- The canonical map `A ⊗[B, f] Q → P` is bijective. -/
  isIso_tensor : Function.Bijective (canonicalTensorMap baseHom toRingHom commutes)

namespace Hom

/-- Package a base morphism and an `f`-linear ring map inducing a base-change isomorphism. -/
def of {Q P : FlatAlgebraCat Λ k} (baseHom : Q.base ⟶ P.base)
    (toRingHom : Q.algebra →+* P.algebra)
    (commutes :
      toRingHom.comp (algebraMap Q.base.carrier Q.algebra) =
        (algebraMap P.base.carrier P.algebra).comp baseHom.hom.toRingHom)
    (isIso_tensor : Function.Bijective (canonicalTensorMap baseHom toRingHom commutes)) :
    Hom Q P where
  baseHom := baseHom
  toRingHom := toRingHom
  commutes := commutes
  isIso_tensor := isIso_tensor

/-- Identity morphism of a pair `(A, P)`. -/
def id (P : FlatAlgebraCat Λ k) : Hom P P where
  baseHom := 𝟙 P.base
  toRingHom := RingHom.id P.algebra
  commutes := sorry
  isIso_tensor := sorry

/-- Composition of morphisms of pairs. -/
def comp {Q P R : FlatAlgebraCat Λ k} (f : Hom Q P) (g : Hom P R) : Hom Q R where
  baseHom := f.baseHom ≫ g.baseHom
  toRingHom := g.toRingHom.comp f.toRingHom
  commutes := sorry
  isIso_tensor := sorry

/-- A morphism is an `f`-linear ring map whose canonical tensor lift is bijective. -/
theorem spec {Q P : FlatAlgebraCat Λ k} (f : Hom Q P) :
    f.toRingHom.comp (algebraMap Q.base.carrier Q.algebra) =
        (algebraMap P.base.carrier P.algebra).comp f.baseHom.hom.toRingHom ∧
      Function.Bijective (canonicalTensorMap f.baseHom f.toRingHom f.commutes) := sorry

/-- The identity morphism has identity base arrow. -/
theorem id_baseHom (P : FlatAlgebraCat Λ k) : (id P).baseHom = 𝟙 P.base := sorry

/-- Composition of morphisms has composed base arrows. -/
theorem comp_baseHom {Q P R : FlatAlgebraCat Λ k} (f : Hom Q P) (g : Hom P R) :
    (comp f g).baseHom = f.baseHom ≫ g.baseHom := sorry

end Hom

/-- Category of pairs `(A, P)` with cartesian algebra maps. -/
instance category : Category.{u} (FlatAlgebraCat Λ k) where
  Hom := Hom
  id := Hom.id
  comp f g := Hom.comp f g
  id_comp := sorry
  comp_id := sorry
  assoc := sorry

/-- The functor `p` sending `(A, P)` to `A` and `(f, g)` to `f`. -/
def forget : FlatAlgebraCat Λ k ⥤ ArtinianLocalAlgCat Λ k where
  obj X := X.base
  map f := f.baseHom
  map_id := sorry
  map_comp := sorry

/-- The forgetful functor evaluates to the stored base algebra. -/
theorem forget_obj (X : FlatAlgebraCat Λ k) : forget.obj X = X.base := sorry

/-- The forgetful functor sends a morphism to its base arrow. -/
theorem forget_map {Q P : FlatAlgebraCat Λ k} (f : Q ⟶ P) : forget.map f = f.baseHom := sorry

/-- The projection `p : F ⥤ C_Λ` is cofibered in groupoids. -/
instance instIsFiberedInGroupoids_forget :
    IsFibered.InGroupoids
      (forget : FlatAlgebraCat Λ k ⥤ ArtinianLocalAlgCat Λ k).op := sorry

/-- Restriction of scalars along the residue identification, so a `k`-algebra is an
algebra over the residue object of `ArtinianLocalAlgCat`. -/
instance instAlgebraResidueCarrier (P : Type u) [CommRing P] [Algebra k P] :
    Algebra (ArtinianLocalAlgCat.residue Λ k).carrier P :=
  inferInstanceAs (Algebra k P)

/-- Vector spaces over the residue field are free modules over the residue carrier. -/
instance instModuleFreeResidueCarrier (P : Type u) [CommRing P] [Algebra k P] :
    Module.Free (ArtinianLocalAlgCat.residue Λ k).carrier P :=
  inferInstanceAs (Module.Free k P)

/-- A commutative algebra over a field is flat as a module over the residue object. -/
instance instModuleFlatResidueCarrier (P : Type u) [CommRing P] [Algebra k P] :
    Module.Flat (ArtinianLocalAlgCat.residue Λ k).carrier P :=
  Module.Flat.of_free

variable (Λ k)

/-- The object `x0 = (k, P)` of `F`. -/
def ofResidue (P : Type u) [CommRing P] [Algebra k P] : FlatAlgebraCat Λ k :=
  of (ArtinianLocalAlgCat.residue Λ k) P

/-- The base of `ofResidue P` is the residue object of `C_Λ`. -/
theorem ofResidue_base (P : Type u) [CommRing P] [Algebra k P] :
    (ofResidue Λ k P).base = ArtinianLocalAlgCat.residue Λ k := sorry

/-- `x0 = (k, P)` as an object of the residue fibre of `forget`. -/
def residueObj (P : Type u) [CommRing P] [Algebra k P] :
    forget.Fiber (ArtinianLocalAlgCat.residue Λ k) :=
  Fiber.mk (rfl : forget.obj (ofResidue Λ k P) = ArtinianLocalAlgCat.residue Λ k)

/-- The residue-fibre object is included as `ofResidue P`. -/
theorem residueObj_fiberInclusion (P : Type u) [CommRing P] [Algebra k P] :
    Fiber.fiberInclusion.obj (residueObj Λ k P) = ofResidue Λ k P := sorry

/-- The deformation category `Def_P = F_{x0}` is the Over-slice at `x0 = (k, P)`. -/
abbrev deformationCategory (P : Type u) [CommRing P] [Algebra k P] :=
  Over (Fiber.fiberInclusion.obj (residueObj Λ k P))

/-- `deformationCategory P` is the Over-slice of the residue-fibre object `x0 = (k, P)`. -/
theorem deformationCategory_spec (P : Type u) [CommRing P] [Algebra k P] :
    deformationCategory Λ k P = Over (Fiber.fiberInclusion.obj (residueObj Λ k P)) := sorry

end FlatAlgebraCat
