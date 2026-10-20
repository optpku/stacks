module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Adjunction
public import Mathlib.Algebra.Category.ModuleCat.Ulift
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import Mathlib.CategoryTheory.Monoidal.Functor
public import Mathlib.CategoryTheory.Monoidal.NaturalTransformation
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import ReasLib.Algebra.Category.ModuleCat.ChangeOfRings.Exact
public import ReasLib.Algebra.Category.ModuleCat.ChangeOfRings.Monoidal
public import ReasLib.Algebra.Category.ModuleCat.FinitePresentation
public import ReasLib.Algebra.Category.ModuleCat.FinitePresentation.Monoidal

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty
open CategoryTheory.Functor.Monoidal CategoryTheory.MonoidalCategory TensorProduct

universe u v

namespace ModuleCat

variable {A : Type u} [CommRing A] {B : Type v} [CommRing B]

/-- Extension of scalars along `φ : A →+* B` preserves finite presentation of modules. -/
theorem extendScalars_isFinitePresentation (φ : A →+* B)
    (M : ModuleCat.{max u v} A)
    (hM : isFinitePresentation.{u, max u v} A M) :
    isFinitePresentation.{v, max u v} B ((extendScalars φ).obj M) := sorry

/-- Restriction of extension of scalars to finitely presented modules. -/
noncomputable def fpExtendScalars (φ : A →+* B) :
    (isFinitePresentation.{u, max u v} A).FullSubcategory ⥤
      (isFinitePresentation.{v, max u v} B).FullSubcategory :=
  (isFinitePresentation.{v, max u v} B).lift
    ((isFinitePresentation.{u, max u v} A).ι ⋙ extendScalars φ) fun X ↦
    extendScalars_isFinitePresentation φ X.obj X.property

/-- The unit comparison for extension of scalars on the tensor unit. -/
noncomputable def fpExtendScalars.εLinearEquiv (φ : A →+* B) :
    ULift.{u, v} B ≃ₗ[B] (extendScalars φ).obj (of A (ULift.{v, u} A)) :=
  -- Local instance justification (noncanonical choice): φ selects the algebra structure required by the tensor-unit comparison API.
  letI : Algebra A B := φ.toAlgebra
  -- Local instance justification (proof-local temporary data): the tensor-unit comparison requires the scalar-tower proof for the B-module restricted along φ.
  letI : IsScalarTower A B ((restrictScalars φ).obj (of B B)) :=
    IsScalarTower.of_algebraMap_smul fun a c => by
      rw [RingHom.algebraMap_toAlgebra]
      rfl
  (ULift.moduleEquiv : ULift.{u, v} B ≃ₗ[B] B).trans <|
    (AlgebraTensorModule.rid A B
        ((restrictScalars φ).obj (of B B))).symm.trans <|
      AlgebraTensorModule.congr
        (LinearEquiv.refl B ((restrictScalars φ).obj (of B B)))
        (ULift.moduleEquiv : ULift.{v, u} A ≃ₗ[A] A).symm

/-- The unit isomorphism for extension of scalars on finitely presented modules. -/
noncomputable def fpExtendScalars.εIsoData (φ : A →+* B) :
    𝟙_ (isFinitePresentation.{v, max u v} B).FullSubcategory ≅
      (fpExtendScalars φ).obj
        (𝟙_ (isFinitePresentation.{u, max u v} A).FullSubcategory) :=
  ObjectProperty.isoMk _ (LinearEquiv.toModuleIso (fpExtendScalars.εLinearEquiv φ))

/-- The tensorator equivalence for extension of scalars on finitely presented modules. -/
noncomputable def fpExtendScalars.μLinearEquiv (φ : A →+* B)
    (X Y : (isFinitePresentation.{u, max u v} A).FullSubcategory) :
    ((fpExtendScalars φ).obj X ⊗ (fpExtendScalars φ).obj Y).obj ≃ₗ[B]
      ((fpExtendScalars φ).obj (X ⊗ Y)).obj :=
  -- Local instance justification (noncanonical choice): φ.toAlgebra selects the algebra structure required by AlgebraTensorModule.distribBaseChange.
  letI : Algebra A B := φ.toAlgebra
  (AlgebraTensorModule.distribBaseChange A B X.obj Y.obj).symm

/-- The tensorator isomorphism for extension of scalars on finitely presented modules. -/
noncomputable def fpExtendScalars.μIsoData (φ : A →+* B)
    (X Y : (isFinitePresentation.{u, max u v} A).FullSubcategory) :
    (fpExtendScalars φ).obj X ⊗ (fpExtendScalars φ).obj Y ≅
      (fpExtendScalars φ).obj (X ⊗ Y) :=
  ObjectProperty.isoMk _ (LinearEquiv.toModuleIso (fpExtendScalars.μLinearEquiv φ X Y))

/-- The restricted extension-of-scalars functor is monoidal. -/
noncomputable instance fpExtendScalars.instMonoidal (φ : A →+* B) :
    (fpExtendScalars φ).Monoidal :=
  Functor.CoreMonoidal.toMonoidal
    { εIso := fpExtendScalars.εIsoData φ
      μIso := fpExtendScalars.μIsoData φ
      μIso_hom_natural_left := sorry
      μIso_hom_natural_right := sorry
      associativity := sorry
      left_unitality := sorry
      right_unitality := sorry }

/-- The restricted extension-of-scalars functor is right exact. -/
instance fpExtendScalars.instPreservesFiniteColimits (φ : A →+* B) :
    PreservesFiniteColimits (fpExtendScalars φ) := sorry

/-- Restriction of extension of scalars agrees with unrestricted extension after inclusion. -/
noncomputable def fpExtendScalars_comp_ι (φ : A →+* B) :
    fpExtendScalars φ ⋙ (isFinitePresentation.{v, max u v} B).ι ≅
      (isFinitePresentation.{u, max u v} A).ι ⋙ extendScalars φ :=
  Iso.refl _

/-- Right-exact monoidal functors between finitely presented module categories. -/
structure RightExactMonoidalFpFunctor (A : Type u) [CommRing A] (B : Type v) [CommRing B] where
  /-- The underlying functor between finitely presented module categories. -/
  functor : (isFinitePresentation.{u, max u v} A).FullSubcategory ⥤
    (isFinitePresentation.{v, max u v} B).FullSubcategory
  /-- The chosen monoidal structure on the underlying functor. -/
  monoidal : functor.Monoidal
  /-- Preservation of finite colimits by the underlying functor. -/
  rightExact : PreservesFiniteColimits functor

/-- A functor with a chosen monoidal structure and preservation of finite colimits defines a
right-exact monoidal functor between finitely presented module categories. -/
def RightExactMonoidalFpFunctor.ofFunctor
    (F : (isFinitePresentation.{u, max u v} A).FullSubcategory ⥤
      (isFinitePresentation.{v, max u v} B).FullSubcategory)
    (monoidal : F.Monoidal) (rightExact : PreservesFiniteColimits F) :
    RightExactMonoidalFpFunctor A B where
  functor := F
  monoidal := monoidal
  rightExact := rightExact

/-- The functor constructed with a chosen monoidal structure stores that structure and
preserves finite colimits. -/
theorem RightExactMonoidalFpFunctor.ofFunctor_spec
    (F : (isFinitePresentation.{u, max u v} A).FullSubcategory ⥤
      (isFinitePresentation.{v, max u v} B).FullSubcategory)
    (monoidal : F.Monoidal) (rightExact : PreservesFiniteColimits F) :
    (RightExactMonoidalFpFunctor.ofFunctor F monoidal rightExact).monoidal = monoidal ∧
      PreservesFiniteColimits
        (RightExactMonoidalFpFunctor.ofFunctor F monoidal rightExact).functor := sorry

/-- Monoidal natural-isomorphism equivalence on right-exact monoidal functors. -/
def fpFunctorIsoSetoid (A : Type u) [CommRing A] (B : Type v) [CommRing B] :
    Setoid (RightExactMonoidalFpFunctor A B) where
  r F G :=
    -- Local instance justification (noncanonical choice): NatTrans.IsMonoidal must use F's stored monoidal structure through its class-parameterized compatibility interface.
    letI := F.monoidal
    -- Local instance justification (noncanonical choice): NatTrans.IsMonoidal must use G's stored monoidal structure rather than an independently inferred choice.
    letI := G.monoidal
    ∃ e : F.functor ≅ G.functor, NatTrans.IsMonoidal e.hom
  iseqv := sorry

/-- Isomorphism classes of right-exact monoidal functors between finitely presented module
categories. -/
abbrev rightExactMonoidalFpIsoClass (A : Type u) [CommRing A] (B : Type v) [CommRing B] :=
  Quotient (fpFunctorIsoSetoid A B)

/-- The isomorphism class represented by a right-exact monoidal functor. -/
def rightExactMonoidalFpIsoClass.mk
    (F : (isFinitePresentation.{u, max u v} A).FullSubcategory ⥤
      (isFinitePresentation.{v, max u v} B).FullSubcategory)
  [hM : F.Monoidal] [hR : PreservesFiniteColimits F] :
    rightExactMonoidalFpIsoClass A B :=
  Quotient.mk (fpFunctorIsoSetoid A B) (RightExactMonoidalFpFunctor.ofFunctor F hM hR)

/-- The class of restricted extension of scalars associated to a ring homomorphism. -/
noncomputable def ringHom_to_rightExactMonoidalFpIsoClass (φ : A →+* B) :
    rightExactMonoidalFpIsoClass A B :=
  rightExactMonoidalFpIsoClass.mk (fpExtendScalars φ)

/-- Every right-exact monoidal functor on finitely presented modules is monoidally naturally
isomorphic to restricted extension of scalars along a ring homomorphism. -/
theorem fpExtendScalars_iso_of
    (F : (isFinitePresentation.{u, max u v} A).FullSubcategory ⥤
      (isFinitePresentation.{v, max u v} B).FullSubcategory)
    [F.Monoidal] [PreservesFiniteColimits F] :
    ∃ φ : A →+* B, ∃ e : F ≅ fpExtendScalars φ, NatTrans.IsMonoidal e.hom := sorry

/-- Monoidally naturally isomorphic restricted extension-of-scalars functors arise from equal
ring homomorphisms. -/
theorem ringHom_eq_of_fpExtendScalars_iso {φ ψ : A →+* B}
    (h : ∃ e : fpExtendScalars φ ≅ fpExtendScalars ψ, NatTrans.IsMonoidal e.hom) :
    φ = ψ := sorry

/-- Ring homomorphisms classify right-exact monoidal functors between finitely presented module
categories up to monoidal natural isomorphism. -/
theorem ringHom_bijective_isoClass_rightExactMonoidalFp :
    Function.Bijective
      (ringHom_to_rightExactMonoidalFpIsoClass :
        (A →+* B) → rightExactMonoidalFpIsoClass A B) := sorry

end ModuleCat
