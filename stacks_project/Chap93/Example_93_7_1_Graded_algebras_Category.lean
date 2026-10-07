module

public import Mathlib.RingTheory.GradedAlgebra.RingHom
public import Mathlib.RingTheory.GradedAlgebra.TensorProduct
public import stacks_project.Chap90.Definition_90_6_2_Predeformation
public import stacks_project.Chap93.Example_93_7_1_Graded_algebras_Algebra

/-!
# Category of finite projective graded algebras over `ArtinianLocalAlgCat`

Objects are pairs `(A, P)` with `A` in `ArtinianLocalAlgCat` and `P` a commutative
`ℕ`-graded `A`-algebra with finite projective pieces. Morphisms are pairs `(f, g)`
with `g` an `f`-linear graded map inducing the canonical base-change isomorphism.
-/

@[expose] public section

open CategoryTheory Functor
open scoped TensorProduct

universe u

variable (Λ k : Type u) [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

/-- An object of the category `F` of pairs `(A, P)` with `A` in `C_Λ` and `P` a
commutative `ℕ`-graded `A`-algebra with finite projective homogeneous pieces. -/
structure FiniteProjectiveGradedAlgebraCat where
  /-- Underlying object of `ArtinianLocalAlgCat Λ k`. -/
  base : ArtinianLocalAlgCat Λ k
  /-- Underlying finite projective graded algebra over the base. -/
  algebra : FiniteProjectiveGradedAlgebra base.carrier

namespace FiniteProjectiveGradedAlgebraCat

variable {Λ k}

/-- Pair an Artinian local algebra with a finite projective graded algebra over it. -/
def of (A : ArtinianLocalAlgCat Λ k) (P : FiniteProjectiveGradedAlgebra A.carrier) :
    FiniteProjectiveGradedAlgebraCat Λ k where
  base := A
  algebra := P

/-- An object of `F` is a pair consisting of a base in `C_Λ` and a finite projective
graded algebra over that base. -/
theorem spec (X : FiniteProjectiveGradedAlgebraCat Λ k) :
    GradedAlgebra.IsFiniteProjective X.algebra.grading ∧
      (∀ d, Module.Finite X.base.carrier (X.algebra.grading d)) ∧
      ∀ d, Module.Projective X.base.carrier (X.algebra.grading d) := sorry

/-- The `B`-algebra structure on `A` along a morphism `f : B ⟶ A` in `C_Λ`. -/
abbrev algebraAlong {Q P : FiniteProjectiveGradedAlgebraCat Λ k} (f : Q.base ⟶ P.base) :
    Algebra Q.base.carrier P.base.carrier :=
  Algebra.compHom P.base.carrier f.hom.toRingHom

/-- The `B`-algebra structure on `P` along a morphism `f : B ⟶ A` in `C_Λ`. -/
abbrev compAlgebraAlong {Q P : FiniteProjectiveGradedAlgebraCat Λ k} (f : Q.base ⟶ P.base) :
    Algebra Q.base.carrier P.algebra.carrier :=
  Algebra.compHom P.algebra.carrier f.hom.toRingHom

/-- Restriction of scalars along `f` acts by the underlying ring map of `f`. -/
theorem algebraAlong_algebraMap {Q P : FiniteProjectiveGradedAlgebraCat Λ k}
    (f : Q.base ⟶ P.base) :
    (algebraAlong f).algebraMap = f.hom.toRingHom := sorry

/-- The base-change carrier `A ⊗[B] Q` along `f : B ⟶ A`. -/
def tensorAlong {Q P : FiniteProjectiveGradedAlgebraCat Λ k} (f : Q.base ⟶ P.base) : Type u :=
  -- Local instance justification (noncanonical choice): the `B`-algebra structure on `A` is determined by the morphism `f` and cannot be a global instance.
  letI := algebraAlong f
  P.base.carrier ⊗[Q.base.carrier] Q.algebra.carrier

/-- Pure tensors in the base-change carrier along `f`. -/
def tmulAlong {Q P : FiniteProjectiveGradedAlgebraCat Λ k} (f : Q.base ⟶ P.base)
    (a : P.base.carrier) (q : Q.algebra.carrier) : tensorAlong f :=
  -- Local instance justification (noncanonical choice): the `B`-algebra structure on `A` is determined by the morphism `f` and cannot be a global instance.
  letI := algebraAlong f
  a ⊗ₜ[Q.base.carrier] q

/-- The canonical `A`-linear map `A ⊗[B, f] Q → P` induced by an `f`-linear graded map. -/
def canonicalTensorMap {Q P : FiniteProjectiveGradedAlgebraCat Λ k}
    (f : Q.base ⟶ P.base) (g : Q.algebra.grading →+*ᵍ P.algebra.grading)
    (h_commutes :
      g.toRingHom.comp (algebraMap Q.base.carrier Q.algebra.carrier) =
        (algebraMap P.base.carrier P.algebra.carrier).comp f.hom.toRingHom) :
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
        (algebraMap P.base.carrier P.algebra.carrier).comp f.hom.toRingHom)
    (a : P.base.carrier) (q : Q.algebra.carrier) :
    canonicalTensorMap f g h_commutes (tmulAlong f a q) = a • g q := sorry

/-- A morphism `(f, g) : (B, Q) ⟶ (A, P)` is a morphism `f : B ⟶ A` in `C_Λ` together
with an `f`-linear graded map `g : Q → P` inducing an isomorphism `Q ⊗_{B, f} A ≅ P`. -/
structure Hom (Q P : FiniteProjectiveGradedAlgebraCat Λ k) where
  /-- Underlying morphism of Artinian local algebras. -/
  baseHom : Q.base ⟶ P.base
  /-- Underlying graded ring homomorphism. -/
  gradedHom : Q.algebra.grading →+*ᵍ P.algebra.grading
  /-- `f`-linearity as the algebra-map square. -/
  commutes :
    gradedHom.toRingHom.comp (algebraMap Q.base.carrier Q.algebra.carrier) =
      (algebraMap P.base.carrier P.algebra.carrier).comp baseHom.hom.toRingHom
  /-- The canonical map `A ⊗[B, f] Q → P` is bijective. -/
  isIso_tensor : Function.Bijective (canonicalTensorMap baseHom gradedHom commutes)

namespace Hom

/-- Package a base morphism and an `f`-linear graded map inducing a base-change isomorphism. -/
def of {Q P : FiniteProjectiveGradedAlgebraCat Λ k} (baseHom : Q.base ⟶ P.base)
    (gradedHom : Q.algebra.grading →+*ᵍ P.algebra.grading)
    (commutes :
      gradedHom.toRingHom.comp (algebraMap Q.base.carrier Q.algebra.carrier) =
        (algebraMap P.base.carrier P.algebra.carrier).comp baseHom.hom.toRingHom)
    (isIso_tensor : Function.Bijective (canonicalTensorMap baseHom gradedHom commutes)) :
    Hom Q P where
  baseHom := baseHom
  gradedHom := gradedHom
  commutes := commutes
  isIso_tensor := isIso_tensor

/-- Identity morphism of a pair `(A, P)`. -/
def id (P : FiniteProjectiveGradedAlgebraCat Λ k) : Hom P P where
  baseHom := 𝟙 P.base
  gradedHom := GradedRingHom.id P.algebra.grading
  commutes := sorry
  isIso_tensor := sorry

/-- Composition of morphisms of pairs. -/
def comp {Q P R : FiniteProjectiveGradedAlgebraCat Λ k} (f : Hom Q P) (g : Hom P R) : Hom Q R where
  baseHom := f.baseHom ≫ g.baseHom
  gradedHom := g.gradedHom.comp f.gradedHom
  commutes := sorry
  isIso_tensor := sorry

/-- A morphism is an `f`-linear graded map whose canonical tensor lift is bijective. -/
theorem spec {Q P : FiniteProjectiveGradedAlgebraCat Λ k} (f : Hom Q P) :
    f.gradedHom.toRingHom.comp (algebraMap Q.base.carrier Q.algebra.carrier) =
        (algebraMap P.base.carrier P.algebra.carrier).comp f.baseHom.hom.toRingHom ∧
      (∀ d x, x ∈ Q.algebra.grading d → f.gradedHom x ∈ P.algebra.grading d) ∧
      Function.Bijective (canonicalTensorMap f.baseHom f.gradedHom f.commutes) := sorry

/-- The identity morphism has identity base arrow. -/
theorem id_baseHom (P : FiniteProjectiveGradedAlgebraCat Λ k) :
    (id P).baseHom = 𝟙 P.base := sorry

/-- Composition of morphisms has composed base arrows. -/
theorem comp_baseHom {Q P R : FiniteProjectiveGradedAlgebraCat Λ k} (f : Hom Q P) (g : Hom P R) :
    (comp f g).baseHom = f.baseHom ≫ g.baseHom := sorry

end Hom

/-- Category of pairs `(A, P)` with cartesian graded algebra maps. -/
instance category : Category.{u} (FiniteProjectiveGradedAlgebraCat Λ k) where
  Hom := Hom
  id := Hom.id
  comp f g := Hom.comp f g
  id_comp := sorry
  comp_id := sorry
  assoc := sorry

/-- The functor `p` sending `(A, P)` to `A` and `(f, g)` to `f`. -/
def forget : FiniteProjectiveGradedAlgebraCat Λ k ⥤ ArtinianLocalAlgCat Λ k where
  obj X := X.base
  map f := f.baseHom
  map_id := sorry
  map_comp := sorry

/-- The forgetful functor evaluates to the stored base algebra. -/
theorem forget_obj (X : FiniteProjectiveGradedAlgebraCat Λ k) :
    forget.obj X = X.base := sorry

/-- The forgetful functor sends a morphism to its base arrow. -/
theorem forget_map {Q P : FiniteProjectiveGradedAlgebraCat Λ k} (f : Q ⟶ P) :
    forget.map f = f.baseHom := sorry

/-- The projection `p : F ⥤ C_Λ` is cofibered in groupoids. -/
instance instIsFiberedInGroupoids_forget :
    IsFibered.InGroupoids
      (forget : FiniteProjectiveGradedAlgebraCat Λ k ⥤ ArtinianLocalAlgCat Λ k).op := sorry

variable (Λ)

/-- The object `x0 = (k, P)` of `F`. -/
def ofResidue (P : FiniteProjectiveGradedAlgebra k) : FiniteProjectiveGradedAlgebraCat Λ k :=
  of (ArtinianLocalAlgCat.residue Λ k) P

/-- The base of `ofResidue P` is the residue object of `C_Λ`. -/
theorem ofResidue_base (P : FiniteProjectiveGradedAlgebra k) :
    (ofResidue Λ P).base = ArtinianLocalAlgCat.residue Λ k := sorry

/-- `x0 = (k, P)` as an object of the residue fibre of `forget`. -/
def residueObj (P : FiniteProjectiveGradedAlgebra k) :
    forget.Fiber (ArtinianLocalAlgCat.residue Λ k) :=
  Fiber.mk (rfl : forget.obj (ofResidue Λ P) = ArtinianLocalAlgCat.residue Λ k)

/-- The residue-fibre object is included as `ofResidue P`. -/
theorem residueObj_fiberInclusion (P : FiniteProjectiveGradedAlgebra k) :
    Fiber.fiberInclusion.obj (residueObj Λ P) = ofResidue Λ P := sorry

end FiniteProjectiveGradedAlgebraCat
