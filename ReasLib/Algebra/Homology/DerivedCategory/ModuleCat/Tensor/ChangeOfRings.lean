module

public import ReasLib.Algebra.Homology.DerivedCategory.ScalarExtension
public import ReasLib.Algebra.Homology.DerivedCategory.TensorProduct
import Mathlib.Tactic.CrossRefAttribute

/-!
# Derived tensor product under change of rings

For a ring map `R ⟶ A` and a fixed object of `D(A)`, this leaf packages derived scalar
extension followed by the fixed-right derived tensor product.  The resulting functor is the
canonical owner of the change-of-rings notation `K ⊗[R]^L[A] N`.

@stack 06Y6
@stack 0BYK
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace CategoryTheory

variable {R A : Type u} [CommRing R] [CommRing A]

local notation "DModA" => DerivedCategory (ModuleCat A)

/-- Lemma 15.60.1 (1): for a ring map `σ : R ⟶ A` and `N : D(A)`, derived tensoring over
`R` with target `N` is derived scalar extension followed by derived tensoring over `A`. -/
@[stacks 06Y6 "(1) derived change-of-rings functor"]
noncomputable def derivedTensorChangeOfRings (σ : R →+* A) (N : DModA) :
    DerivedCategory (ModuleCat R) ⥤ DModA :=
  ModuleCat.derivedExtensionOfScalars σ ⋙ DerivedCategory.derivedTensorProduct N

namespace DerivedTensorChangeOfRings

/- The source-facing notation for the derived change-of-rings object. -/
set_option quotPrecheck false in
scoped notation:70 K:70 " ⊗[" R:70 "]^L[" A:70 "] " N:71 =>
  (CategoryTheory.derivedTensorChangeOfRings (algebraMap R A) N).obj K

end DerivedTensorChangeOfRings

/-- The canonical change-of-rings functor commutes with integer shifts. -/
@[stacks 06Y6 "shift compatibility of derived tensor change of rings"]
noncomputable instance derivedTensorChangeOfRings_commShift (σ : R →+* A) (N : DModA) :
    (derivedTensorChangeOfRings σ N).CommShift ℤ :=
  Functor.CommShift.comp (ModuleCat.derivedExtensionOfScalars σ)
    (DerivedCategory.derivedTensorProduct N)

/-- Lemma 15.60.1 (2): derived tensor product under change of rings is an exact functor of
triangulated derived categories. -/
@[stacks 06Y6 "(2) triangulated exactness"]
theorem derivedTensorChangeOfRings_isTriangulated (σ : R →+* A) (N : DModA) :
    (derivedTensorChangeOfRings σ N).IsTriangulated := sorry

/-- Lemma 15.60.1 (3): objectwise, change-of-rings derived tensor product is scalar extension
followed by the derived tensor product over the target ring. -/
@[stacks 06Y6 "(3) scalar-extension factorization"]
noncomputable def derivedTensorChangeOfRingsObjIso
    (σ : R →+* A) (N : DModA) (K : DerivedCategory (ModuleCat R)) :
    (derivedTensorChangeOfRings σ N).obj K ≅
      (DerivedCategory.derivedTensorProduct N).obj
        ((ModuleCat.derivedExtensionOfScalars σ).obj K) :=
  Iso.refl _

/-- A morphism in the fixed right argument induces a natural transformation between the
corresponding change-of-rings functors. -/
@[stacks 0BYK "derived tensor change-of-rings transformation"]
noncomputable def derivedTensorChangeOfRingsMap
    (σ : R →+* A) {L N : DModA} (f : L ⟶ N) :
    derivedTensorChangeOfRings σ L ⟶ derivedTensorChangeOfRings σ N :=
  Functor.whiskerLeft (ModuleCat.derivedExtensionOfScalars σ)
    ((DerivedCategory.DerivedTensorProduct.bifunctorIso L).hom ≫
      (Functor.curry.obj
        (DerivedCategory.DerivedTensor.Bifunctor.functor (C := ModuleCat A))).flip.map f ≫
      (DerivedCategory.DerivedTensorProduct.bifunctorIso N).inv)

/-- The component of `derivedTensorChangeOfRingsMap` is the canonical two-variable derived
tensor map on `(𝟙,f)`, transported through the fixed-right comparisons. -/
theorem derivedTensorChangeOfRingsMap_app
    (σ : R →+* A) {L N : DModA} (f : L ⟶ N) (K : DerivedCategory (ModuleCat R)) :
    (derivedTensorChangeOfRingsMap σ f).app K =
      (DerivedCategory.DerivedTensorProduct.objIsoBifunctor
          ((ModuleCat.derivedExtensionOfScalars σ).obj K) L).hom ≫
        (DerivedCategory.DerivedTensor.Bifunctor.functor (C := ModuleCat A)).map
          (Prod.mkHom (𝟙 _) f) ≫
        (DerivedCategory.DerivedTensorProduct.objIsoBifunctor
          ((ModuleCat.derivedExtensionOfScalars σ).obj K) N).inv := sorry

/-- Lemma 15.60.2 (1): a map of complexes of `A`-modules induces a natural transformation
between the corresponding change-of-rings derived tensor functors. -/
@[stacks 0BYK "(1) induced derived tensor transformation"]
noncomputable def derivedTensorChangeOfRingsMapOfComplex
    (σ : R →+* A) {L N : CochainComplex (ModuleCat A) ℤ} (f : L ⟶ N) :
    derivedTensorChangeOfRings σ (DerivedCategory.Q.obj L) ⟶
      derivedTensorChangeOfRings σ (DerivedCategory.Q.obj N) :=
  derivedTensorChangeOfRingsMap σ (DerivedCategory.Q.map f)

/-- An isomorphism in the fixed right argument induces an isomorphism of change-of-rings
functors. -/
theorem derivedTensorChangeOfRingsMap_isIso
    (σ : R →+* A) {L N : DModA} (f : L ⟶ N) [IsIso f] :
    IsIso (derivedTensorChangeOfRingsMap σ f) := sorry

/-- Lemma 15.60.2 (2): a quasi-isomorphism of complexes induces an isomorphism of
change-of-rings derived tensor functors. -/
@[stacks 0BYK "(2) quasi-isomorphism induces a functor isomorphism"]
theorem derivedTensorChangeOfRingsMapOfComplex_isIso
    (σ : R →+* A) {L N : CochainComplex (ModuleCat A) ℤ} (f : L ⟶ N) [QuasiIso f] :
    IsIso (derivedTensorChangeOfRingsMapOfComplex σ f) := sorry

end CategoryTheory
