/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.FiberedCategory.Fiber
public import Mathlib.RingTheory.GradedAlgebra.RingHom
public import Mathlib.RingTheory.GradedAlgebra.TensorProduct
public import ReasLib.AlgebraicGeometry.FormalDeformation.ArtinianLocal.Residue
public import ReasLib.CategoryTheory.Fibered.InGroupoids.Basic
public import ReasLib.RingTheory.GradedAlgebra.FiniteProjective

/-!
# Finite projective graded algebras over Artinian local bases

The category of finite projective graded algebras with base-change-isomorphism morphisms,
its projection to Artinian local algebras, and the slice at a residue-field algebra.
-/

@[expose] public section

open CategoryTheory Functor
open scoped TensorProduct

universe u

variable (Λ k : Type u) [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

/-- An Artinian local base together with a finite projective commutative graded algebra. -/
def FiniteProjectiveGradedAlgebraCat :=
  Σ' base : ArtinianLocalAlgCat Λ k, FiniteProjectiveGradedAlgebra base.carrier

namespace FiniteProjectiveGradedAlgebraCat

variable {Λ k}

/-- The Artinian local base of a graded algebra. -/
def base (P : FiniteProjectiveGradedAlgebraCat Λ k) : ArtinianLocalAlgCat Λ k := P.1

/-- The finite projective graded algebra over the stored base. -/
def algebra (P : FiniteProjectiveGradedAlgebraCat Λ k) :
    FiniteProjectiveGradedAlgebra P.base.carrier := P.2

/-- Pair an Artinian local algebra with a finite projective graded algebra over it. -/
def of (A : ArtinianLocalAlgCat Λ k) (P : FiniteProjectiveGradedAlgebra A.carrier) :
    FiniteProjectiveGradedAlgebraCat Λ k := ⟨A, P⟩

/-- Every homogeneous piece is finite projective over the stored Artinian local base. -/
theorem spec (X : FiniteProjectiveGradedAlgebraCat Λ k) :
    GradedAlgebra.IsFiniteProjective X.algebra.grading ∧
      (∀ d, Module.Finite X.base.carrier (X.algebra.grading d)) ∧
      ∀ d, Module.Projective X.base.carrier (X.algebra.grading d) := sorry

/-- The algebra structure on the target base obtained by restriction along a base arrow. -/
abbrev algebraAlong {Q P : FiniteProjectiveGradedAlgebraCat Λ k} (f : Q.base ⟶ P.base) :
    Algebra Q.base.carrier P.base.carrier :=
  Algebra.compHom P.base.carrier (ArtinianLocalAlgCat.Hom.toRingHom f)

/-- The algebra structure on the target graded algebra restricted along a base arrow. -/
abbrev compAlgebraAlong {Q P : FiniteProjectiveGradedAlgebraCat Λ k}
    (f : Q.base ⟶ P.base) : Algebra Q.base.carrier P.algebra.carrier :=
  Algebra.compHom P.algebra.carrier (ArtinianLocalAlgCat.Hom.toRingHom f)

/-- Restriction of scalars along a base arrow uses its underlying ring homomorphism. -/
theorem algebraAlong_algebraMap {Q P : FiniteProjectiveGradedAlgebraCat Λ k}
    (f : Q.base ⟶ P.base) :
    (algebraAlong f).algebraMap = ArtinianLocalAlgCat.Hom.toRingHom f := sorry

/-- The base-change carrier `A ⊗[B] Q` along a base arrow `B ⟶ A`. -/
def tensorAlong {Q P : FiniteProjectiveGradedAlgebraCat Λ k} (f : Q.base ⟶ P.base) : Type u :=
  -- Local instance justification (noncanonical choice): the `B`-algebra structure on `A` is determined by the morphism `f` and cannot be a global instance.
  letI := algebraAlong f
  P.base.carrier ⊗[Q.base.carrier] Q.algebra.carrier

/-- Pure tensors in the base-change carrier along a base arrow. -/
def tmulAlong {Q P : FiniteProjectiveGradedAlgebraCat Λ k} (f : Q.base ⟶ P.base)
    (a : P.base.carrier) (q : Q.algebra.carrier) : tensorAlong f :=
  -- Local instance justification (noncanonical choice): the `B`-algebra structure on `A` is determined by the morphism `f` and cannot be a global instance.
  letI := algebraAlong f
  a ⊗ₜ[Q.base.carrier] q

/-- The canonical tensor lift of a scalar-compatible graded ring map. -/
def canonicalTensorMap {Q P : FiniteProjectiveGradedAlgebraCat Λ k}
    (f : Q.base ⟶ P.base) (g : Q.algebra.grading →+*ᵍ P.algebra.grading)
    (h_commutes :
      g.toRingHom.comp (algebraMap Q.base.carrier Q.algebra.carrier) =
        (algebraMap P.base.carrier P.algebra.carrier).comp
          (ArtinianLocalAlgCat.Hom.toRingHom f)) :
    tensorAlong f → P.algebra.carrier :=
  -- Local instance justification (noncanonical choice): the `B`-algebra structure on `A` is determined by the morphism `f` and cannot be a global instance.
  letI := algebraAlong f
  -- Local instance justification (noncanonical choice): the `B`-algebra structure on `P` is determined by the morphism `f` and cannot be a global instance.
  letI := compAlgebraAlong f
  -- Local instance justification (noncanonical choice): the scalar tower `B → A → P` is determined by the morphism `f` and cannot be a global instance.
  letI : IsScalarTower Q.base.carrier P.base.carrier P.algebra.carrier :=
    IsScalarTower.of_algebraMap_eq' rfl
  fun x ↦
    GradedAlgHom.liftEquiv Q.algebra.grading P.algebra.grading
      { g.toRingHom with
        commutes' := fun r ↦ RingHom.ext_iff.mp h_commutes r
        map_mem := g.map_mem } x

/-- The canonical tensor map sends `a ⊗ q` to `a • g q`. -/
theorem canonicalTensorMap_tmul {Q P : FiniteProjectiveGradedAlgebraCat Λ k}
    (f : Q.base ⟶ P.base) (g : Q.algebra.grading →+*ᵍ P.algebra.grading)
    (h_commutes :
      g.toRingHom.comp (algebraMap Q.base.carrier Q.algebra.carrier) =
        (algebraMap P.base.carrier P.algebra.carrier).comp
          (ArtinianLocalAlgCat.Hom.toRingHom f))
    (a : P.base.carrier) (q : Q.algebra.carrier) :
    canonicalTensorMap f g h_commutes (tmulAlong f a q) = a • g q := sorry

/-- A scalar-compatible graded map over a base arrow whose canonical tensor lift is bijective. -/
def Hom (Q P : FiniteProjectiveGradedAlgebraCat Λ k) :=
  Σ' baseHom : Q.base ⟶ P.base,
    Σ' gradedHom : Q.algebra.grading →+*ᵍ P.algebra.grading,
      Σ' commutes :
        gradedHom.toRingHom.comp (algebraMap Q.base.carrier Q.algebra.carrier) =
          (algebraMap P.base.carrier P.algebra.carrier).comp
            (ArtinianLocalAlgCat.Hom.toRingHom baseHom),
        Function.Bijective (canonicalTensorMap baseHom gradedHom commutes)

namespace Hom

/-- The base arrow of a finite projective graded algebra morphism. -/
def baseHom {Q P : FiniteProjectiveGradedAlgebraCat Λ k} (f : Hom Q P) :
    Q.base ⟶ P.base := f.1

/-- The graded ring map of a finite projective graded algebra morphism. -/
def gradedHom {Q P : FiniteProjectiveGradedAlgebraCat Λ k} (f : Hom Q P) :
    Q.algebra.grading →+*ᵍ P.algebra.grading := f.2.1

/-- The scalar compatibility stored in a finite projective graded algebra morphism. -/
abbrev commutes {Q P : FiniteProjectiveGradedAlgebraCat Λ k} (f : Hom Q P) :
    f.gradedHom.toRingHom.comp (algebraMap Q.base.carrier Q.algebra.carrier) =
      (algebraMap P.base.carrier P.algebra.carrier).comp
        (ArtinianLocalAlgCat.Hom.toRingHom f.baseHom) := f.2.2.1

/-- The bijectivity of the canonical tensor lift stored in a graded algebra morphism. -/
abbrev isIso_tensor {Q P : FiniteProjectiveGradedAlgebraCat Λ k} (f : Hom Q P) :
    Function.Bijective (canonicalTensorMap f.baseHom f.gradedHom f.commutes) := f.2.2.2

/-- Construct a graded algebra morphism from its maps and base-change conditions. -/
def of {Q P : FiniteProjectiveGradedAlgebraCat Λ k} (baseHom : Q.base ⟶ P.base)
    (gradedHom : Q.algebra.grading →+*ᵍ P.algebra.grading)
    (commutes :
      gradedHom.toRingHom.comp (algebraMap Q.base.carrier Q.algebra.carrier) =
        (algebraMap P.base.carrier P.algebra.carrier).comp
          (ArtinianLocalAlgCat.Hom.toRingHom baseHom))
    (isIso_tensor : Function.Bijective (canonicalTensorMap baseHom gradedHom commutes)) :
    Hom Q P := ⟨baseHom, gradedHom, commutes, isIso_tensor⟩

/-- Identity graded ring maps commute with the identity base arrow. -/
theorem id_commutes (P : FiniteProjectiveGradedAlgebraCat Λ k) :
    (GradedRingHom.id P.algebra.grading).toRingHom.comp
        (algebraMap P.base.carrier P.algebra.carrier) =
      (algebraMap P.base.carrier P.algebra.carrier).comp
        (ArtinianLocalAlgCat.Hom.toRingHom (𝟙 P.base)) := sorry

/-- The canonical tensor lift of an identity graded ring map is bijective. -/
theorem id_isIsoTensor (P : FiniteProjectiveGradedAlgebraCat Λ k) :
    Function.Bijective
      (canonicalTensorMap (𝟙 P.base) (GradedRingHom.id P.algebra.grading)
        (id_commutes P)) := sorry

/-- The identity morphism uses identity base and graded ring maps. -/
def id (P : FiniteProjectiveGradedAlgebraCat Λ k) : Hom P P :=
  of (𝟙 P.base) (GradedRingHom.id P.algebra.grading) (id_commutes P) (id_isIsoTensor P)

/-- Composed graded ring maps commute with the composed base arrow. -/
theorem comp_commutes {Q P R : FiniteProjectiveGradedAlgebraCat Λ k}
    (f : Hom Q P) (g : Hom P R) :
    (g.gradedHom.comp f.gradedHom).toRingHom.comp
        (algebraMap Q.base.carrier Q.algebra.carrier) =
      (algebraMap R.base.carrier R.algebra.carrier).comp
        (ArtinianLocalAlgCat.Hom.toRingHom (f.baseHom ≫ g.baseHom)) := sorry

/-- The canonical tensor lift of a composition of graded algebra morphisms is bijective. -/
theorem comp_isIsoTensor {Q P R : FiniteProjectiveGradedAlgebraCat Λ k}
    (f : Hom Q P) (g : Hom P R) :
    Function.Bijective
      (canonicalTensorMap (f.baseHom ≫ g.baseHom) (g.gradedHom.comp f.gradedHom)
        (comp_commutes f g)) := sorry

/-- Compose graded algebra morphisms by composing their base and graded ring maps. -/
def comp {Q P R : FiniteProjectiveGradedAlgebraCat Λ k} (f : Hom Q P) (g : Hom P R) :
    Hom Q R :=
  of (f.baseHom ≫ g.baseHom) (g.gradedHom.comp f.gradedHom)
    (comp_commutes f g) (comp_isIsoTensor f g)

/-- A graded algebra morphism is scalar-compatible, degree-preserving, and a base-change isomorphism. -/
theorem spec {Q P : FiniteProjectiveGradedAlgebraCat Λ k} (f : Hom Q P) :
    f.gradedHom.toRingHom.comp (algebraMap Q.base.carrier Q.algebra.carrier) =
        (algebraMap P.base.carrier P.algebra.carrier).comp
          (ArtinianLocalAlgCat.Hom.toRingHom f.baseHom) ∧
      (∀ d x, x ∈ Q.algebra.grading d → f.gradedHom x ∈ P.algebra.grading d) ∧
      Function.Bijective (canonicalTensorMap f.baseHom f.gradedHom f.commutes) := sorry

/-- The identity morphism has identity base arrow. -/
theorem id_baseHom (P : FiniteProjectiveGradedAlgebraCat Λ k) :
    (id P).baseHom = 𝟙 P.base := sorry

/-- Composition of graded algebra morphisms composes their base arrows. -/
theorem comp_baseHom {Q P R : FiniteProjectiveGradedAlgebraCat Λ k}
    (f : Hom Q P) (g : Hom P R) :
    (comp f g).baseHom = f.baseHom ≫ g.baseHom := sorry

/-- Composing an identity on the left leaves a graded algebra morphism unchanged. -/
theorem id_comp {Q P : FiniteProjectiveGradedAlgebraCat Λ k} (f : Hom Q P) :
    comp (id Q) f = f := sorry

/-- Composing an identity on the right leaves a graded algebra morphism unchanged. -/
theorem comp_id {Q P : FiniteProjectiveGradedAlgebraCat Λ k} (f : Hom Q P) :
    comp f (id P) = f := sorry

/-- Composition of graded algebra morphisms is associative. -/
theorem assoc {Q P R S : FiniteProjectiveGradedAlgebraCat Λ k}
    (f : Hom Q P) (g : Hom P R) (h : Hom R S) :
    comp (comp f g) h = comp f (comp g h) := sorry

end Hom

/-- The category of finite projective graded algebras with base-change-isomorphism morphisms. -/
instance category : Category.{u} (FiniteProjectiveGradedAlgebraCat Λ k) where
  Hom := Hom
  id := Hom.id
  comp f g := Hom.comp f g
  id_comp f := Hom.id_comp f
  comp_id f := Hom.comp_id f
  assoc f g h := Hom.assoc f g h

/-- Project a graded algebra to its base and a morphism to its base arrow. -/
def forget : FiniteProjectiveGradedAlgebraCat Λ k ⥤ ArtinianLocalAlgCat Λ k where
  obj X := X.base
  map f := f.baseHom
  map_id X := Hom.id_baseHom X
  map_comp f g := Hom.comp_baseHom f g

/-- The projection functor evaluates to the stored base algebra. -/
theorem forget_obj (X : FiniteProjectiveGradedAlgebraCat Λ k) :
    forget.obj X = X.base := sorry

/-- The projection functor sends a graded algebra morphism to its base arrow. -/
theorem forget_map {Q P : FiniteProjectiveGradedAlgebraCat Λ k} (f : Q ⟶ P) :
    forget.map f = f.baseHom := sorry

/-- The projection of finite projective graded algebras is cofibered in groupoids. -/
instance instIsFiberedInGroupoids_forget :
    IsFibered.InGroupoids
      (forget : FiniteProjectiveGradedAlgebraCat Λ k ⥤ ArtinianLocalAlgCat Λ k).op := sorry

variable (Λ)

/-- A graded algebra over the residue field, paired with the residue-field base. -/
def ofResidue (P : FiniteProjectiveGradedAlgebra k) : FiniteProjectiveGradedAlgebraCat Λ k :=
  of (ArtinianLocalAlgCat.residue Λ k) P

/-- The base of a residue-field graded algebra is the residue-field object. -/
theorem ofResidue_base (P : FiniteProjectiveGradedAlgebra k) :
    (ofResidue Λ P).base = ArtinianLocalAlgCat.residue Λ k := sorry

/-- A graded algebra over the residue field as an object of the residue fibre. -/
def residueObj (P : FiniteProjectiveGradedAlgebra k) :
    forget.Fiber (ArtinianLocalAlgCat.residue Λ k) :=
  Fiber.mk (rfl : forget.obj (ofResidue Λ P) = ArtinianLocalAlgCat.residue Λ k)

/-- Inclusion of the residue fibre recovers the paired residue-field graded algebra. -/
theorem residueObj_fiberInclusion (P : FiniteProjectiveGradedAlgebra k) :
    Fiber.fiberInclusion.obj (residueObj Λ P) = ofResidue Λ P := sorry

variable (k)

/-- The deformation category is the total-category slice at a residue-field graded algebra. -/
abbrev deformationCategory (P : FiniteProjectiveGradedAlgebra k) :=
  Over (Fiber.fiberInclusion.obj (residueObj Λ P))

/-- The deformation category is the Over-slice of the included residue-fibre object. -/
theorem deformationCategory_spec (P : FiniteProjectiveGradedAlgebra k) :
    deformationCategory Λ k P = Over (Fiber.fiberInclusion.obj (residueObj Λ P)) := sorry

end FiniteProjectiveGradedAlgebraCat
