module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.Functor.Derived.Adjunction
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import Mathlib.CategoryTheory.Sites.Adjunction
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.Sheafification
public import ReasLib.CategoryTheory.Adjunction.HomotopyCategory
public import Mathlib.GroupTheory.Torsion
public import ReasLib.Algebra.Category.ModuleCat.ChangeOfRings.Additive
public import ReasLib.Algebra.Category.ModuleCat.ChangeOfRings.Exact
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Colimit.ChangeOfRings
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Exact
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Exact.Composition
public import ReasLib.CategoryTheory.DerivedCategory.Functor.TotalLeftDerived
public import ReasLib.CategoryTheory.DerivedCategory.Functor.TotalRightDerived.Cochain.ExactFirst
public import ReasLib.CategoryTheory.DerivedCategory.Functor.TotalRightDerived.Homotopy.Naturality
public import ReasLib.CategoryTheory.DerivedCategory.Monoidal.Tensor
public import ReasLib.CategoryTheory.Sites.Pullback.SheafCompose
public import stacks_project.Chap63.Definition_63_12_1_LowerShriek
import Mathlib.Tactic.CrossRefAttribute

/-!
# Change of coefficients on étale derived categories

Restriction of scalars along a ring map `φ : Λ1 →+* Λ2` is exact `sheafCompose` of
`ModuleCat.restrictScalars`. Extension of scalars is sheafification of pointwise
`ModuleCat.extendScalars`, then the total left derived functor.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Functor
open CategoryTheory.Sheaf
open CategoryTheory.MonoidalCategory
open AlgebraicGeometry
open AlgebraicGeometry.Scheme
open ComplexShape
open scoped CategoryTheory.DerivedCategory.DerivedTensor

noncomputable section

universe u v w

namespace AlgebraicGeometry.Scheme.Etale

variable {Λ1 Λ2 : Type u} [CommRing Λ1] [CommRing Λ2] (φ : Λ1 →+* Λ2)

/-- Restriction of scalars on small-étale sheaves of modules along `φ`. -/
abbrev etaleModuleRestrictScalars (X : Scheme.{u})
    [X.smallEtaleTopology.HasSheafCompose (ModuleCat.restrictScalars φ)] :
    Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ2) ⥤
      Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ1) :=
  sheafCompose X.smallEtaleTopology (ModuleCat.restrictScalars φ)

/-- Restriction of scalars on étale sheaves is `sheafCompose` of
`ModuleCat.restrictScalars`. -/
theorem etaleModuleRestrictScalars_def (X : Scheme.{u})
    [X.smallEtaleTopology.HasSheafCompose (ModuleCat.restrictScalars φ)] :
    etaleModuleRestrictScalars φ X =
      sheafCompose X.smallEtaleTopology (ModuleCat.restrictScalars φ) :=
  sorry

/-- Restriction of scalars of étale sheaves of modules is additive. -/
instance etaleModuleRestrictScalars_additive (X : Scheme.{u})
    [X.smallEtaleTopology.HasSheafCompose (ModuleCat.restrictScalars φ)] :
    (etaleModuleRestrictScalars φ X).Additive :=
  sorry

/-- Restriction of scalars of étale sheaves of modules preserves finite limits. -/
instance etaleModuleRestrictScalars_preservesFiniteLimits (X : Scheme.{u})
    [X.smallEtaleTopology.HasSheafCompose (ModuleCat.restrictScalars φ)] :
    PreservesFiniteLimits (etaleModuleRestrictScalars φ X) :=
  sorry

/-- Restriction of scalars of étale sheaves of modules preserves finite colimits. -/
instance etaleModuleRestrictScalars_preservesFiniteColimits (X : Scheme.{u})
    [X.smallEtaleTopology.HasSheafCompose (ModuleCat.restrictScalars φ)] :
    PreservesFiniteColimits (etaleModuleRestrictScalars φ X) :=
  sorry

/-- Small-étale module pushforward is additive whenever the underlying continuous
sheaf pushforward is. -/
instance etaleModulePushforward_additive {X Y : Scheme.{u}} (f : X ⟶ Y)
    {Λ : Type u} [CommRing Λ]
    [((smallEtalePullback f).sheafPushforwardContinuous
        (ModuleCat.{u} Λ) Y.smallEtaleTopology X.smallEtaleTopology).Additive] :
    (etaleModulePushforward f Λ).Additive :=
  sorry

/-- Restriction of scalars on `D(X_étale, -)` along `φ`. -/
def etaleDerivedRestrictScalars (X : Scheme.{u})
    [HasSheafify X.smallEtaleTopology (ModuleCat.{u} Λ1)]
    [HasSheafify X.smallEtaleTopology (ModuleCat.{u} Λ2)]
    [∀ U : X.Etale, HasWeakSheafify (X.smallEtaleTopology.over U) (ModuleCat.{u} Λ1)]
    [∀ U : X.Etale, HasWeakSheafify (X.smallEtaleTopology.over U) (ModuleCat.{u} Λ2)]
    [HasDerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ1))]
    [HasDerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ2))]
    [X.smallEtaleTopology.HasSheafCompose (ModuleCat.restrictScalars φ)] :
    EtaleDerived X Λ2 ⥤ EtaleDerived X Λ1 :=
  (etaleModuleRestrictScalars φ X).mapDerivedCategory

/-- Derived restriction of scalars is `mapDerivedCategory` of the sheaf-level functor. -/
theorem etaleDerivedRestrictScalars_def (X : Scheme.{u})
    [HasSheafify X.smallEtaleTopology (ModuleCat.{u} Λ1)]
    [HasSheafify X.smallEtaleTopology (ModuleCat.{u} Λ2)]
    [∀ U : X.Etale, HasWeakSheafify (X.smallEtaleTopology.over U) (ModuleCat.{u} Λ1)]
    [∀ U : X.Etale, HasWeakSheafify (X.smallEtaleTopology.over U) (ModuleCat.{u} Λ2)]
    [HasDerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ1))]
    [HasDerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ2))]
    [X.smallEtaleTopology.HasSheafCompose (ModuleCat.restrictScalars φ)] :
    etaleDerivedRestrictScalars φ X =
      (etaleModuleRestrictScalars φ X).mapDerivedCategory :=
  sorry

/-- Extension of scalars on small-étale sheaves of modules along `φ`, obtained by
pointwise `ModuleCat.extendScalars` followed by sheafification. -/
def etaleModuleExtendScalars (X : Scheme.{u})
    [HasWeakSheafify X.smallEtaleTopology (ModuleCat.{u} Λ2)] :
    Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ1) ⥤
      Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ2) :=
  sheafToPresheaf X.smallEtaleTopology (ModuleCat.{u} Λ1) ⋙
    DerivedColimit.ChangeOfRings.presheafExtendScalars φ ⋙
    presheafToSheaf X.smallEtaleTopology (ModuleCat.{u} Λ2)

/-- Underived étale extension of scalars sheafifies whiskered `ModuleCat.extendScalars`. -/
theorem etaleModuleExtendScalars_def (X : Scheme.{u})
    [HasWeakSheafify X.smallEtaleTopology (ModuleCat.{u} Λ2)] :
    etaleModuleExtendScalars φ X =
      sheafToPresheaf X.smallEtaleTopology (ModuleCat.{u} Λ1) ⋙
        DerivedColimit.ChangeOfRings.presheafExtendScalars φ ⋙
        presheafToSheaf X.smallEtaleTopology (ModuleCat.{u} Λ2) :=
  sorry

/-- Extension of scalars of étale sheaves of modules is additive. -/
instance etaleModuleExtendScalars_additive (X : Scheme.{u})
    [HasWeakSheafify X.smallEtaleTopology (ModuleCat.{u} Λ2)] :
    (etaleModuleExtendScalars φ X).Additive :=
  sorry

/-- Derived extension of scalars `- ⊗_Λ1^L Λ2 : D(X_étale, Λ1) ⥤ D(X_étale, Λ2)`. -/
def etaleDerivedExtendScalars (X : Scheme.{u})
    [HasSheafify X.smallEtaleTopology (ModuleCat.{u} Λ1)]
    [HasSheafify X.smallEtaleTopology (ModuleCat.{u} Λ2)]
    [∀ U : X.Etale, HasWeakSheafify (X.smallEtaleTopology.over U) (ModuleCat.{u} Λ1)]
    [∀ U : X.Etale, HasWeakSheafify (X.smallEtaleTopology.over U) (ModuleCat.{u} Λ2)]
    [HasDerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ1))]
    [HasDerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ2))]
    [(Functor.Homotopy.toDerived (etaleModuleExtendScalars φ X)).HasLeftDerivedFunctor
      (HomotopyCategory.quasiIso
        (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ1)) (up ℤ))] :
    EtaleDerived X Λ1 ⥤ EtaleDerived X Λ2 :=
  Functor.LeftDerived.Homotopy.functor (etaleModuleExtendScalars φ X)

/-- Derived étale extension of scalars is the total left derived functor of the
sheaf-level extension functor. -/
theorem etaleDerivedExtendScalars_def (X : Scheme.{u})
    [HasSheafify X.smallEtaleTopology (ModuleCat.{u} Λ1)]
    [HasSheafify X.smallEtaleTopology (ModuleCat.{u} Λ2)]
    [∀ U : X.Etale, HasWeakSheafify (X.smallEtaleTopology.over U) (ModuleCat.{u} Λ1)]
    [∀ U : X.Etale, HasWeakSheafify (X.smallEtaleTopology.over U) (ModuleCat.{u} Λ2)]
    [HasDerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ1))]
    [HasDerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ2))]
    [(Functor.Homotopy.toDerived (etaleModuleExtendScalars φ X)).HasLeftDerivedFunctor
      (HomotopyCategory.quasiIso
        (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ1)) (up ℤ))] :
    etaleDerivedExtendScalars φ X =
      Functor.LeftDerived.Homotopy.functor (etaleModuleExtendScalars φ X) :=
  sorry

/-- Sheaf-level extension of scalars is `composeAndSheafify` of `ModuleCat.extendScalars`. -/
theorem etaleModuleExtendScalars_composeAndSheafify (X : Scheme.{u})
    [HasWeakSheafify X.smallEtaleTopology (ModuleCat.{u} Λ2)] :
    etaleModuleExtendScalars φ X =
      Sheaf.composeAndSheafify X.smallEtaleTopology
        (ModuleCat.extendScalars.{u, u, u} φ) :=
  sorry

/-- Extension of scalars is left adjoint to restriction of scalars on étale sheaves. -/
def etaleModuleExtendRestrictAdjunction (X : Scheme.{u})
    [HasWeakSheafify X.smallEtaleTopology (ModuleCat.{u} Λ1)]
    [HasWeakSheafify X.smallEtaleTopology (ModuleCat.{u} Λ2)]
    [X.smallEtaleTopology.HasSheafCompose (ModuleCat.restrictScalars φ)] :
    etaleModuleExtendScalars φ X ⊣ etaleModuleRestrictScalars φ X :=
  Sheaf.adjunction X.smallEtaleTopology
    (ModuleCat.extendRestrictScalarsAdj.{u, u, u} φ)

/-- The sheaf-level change-of-rings adjunction is `Sheaf.adjunction` of
`ModuleCat.extendRestrictScalarsAdj`. -/
theorem etaleModuleExtendRestrictAdjunction_eq (X : Scheme.{u})
    [HasWeakSheafify X.smallEtaleTopology (ModuleCat.{u} Λ1)]
    [HasWeakSheafify X.smallEtaleTopology (ModuleCat.{u} Λ2)]
    [X.smallEtaleTopology.HasSheafCompose (ModuleCat.restrictScalars φ)] :
    etaleModuleExtendRestrictAdjunction φ X =
      Sheaf.adjunction X.smallEtaleTopology
        (ModuleCat.extendRestrictScalarsAdj.{u, u, u} φ) :=
  sorry

/-- Derived extension of scalars is left derived at cochain quasi-isomorphisms. -/
instance etaleDerivedExtendScalars_isLeftDerived (X : Scheme.{u})
    [HasSheafify X.smallEtaleTopology (ModuleCat.{u} Λ1)]
    [HasSheafify X.smallEtaleTopology (ModuleCat.{u} Λ2)]
    [∀ U : X.Etale, HasWeakSheafify (X.smallEtaleTopology.over U) (ModuleCat.{u} Λ1)]
    [∀ U : X.Etale, HasWeakSheafify (X.smallEtaleTopology.over U) (ModuleCat.{u} Λ2)]
    [HasDerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ1))]
    [HasDerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ2))]
    [(Functor.Homotopy.toDerived (etaleModuleExtendScalars φ X)).HasLeftDerivedFunctor
      (HomotopyCategory.quasiIso
        (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ1)) (up ℤ))] :
    (etaleDerivedExtendScalars φ X).IsLeftDerivedFunctor
      (Functor.LeftDerived.Homotopy.cochainCounit (etaleModuleExtendScalars φ X))
      (HomologicalComplex.quasiIso
        (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ1)) (up ℤ)) :=
  Functor.LeftDerived.Homotopy.cochainIsLeftDerived (etaleModuleExtendScalars φ X)

/-- Derived restriction of scalars is right derived at cochain quasi-isomorphisms. -/
instance etaleDerivedRestrictScalars_isRightDerived (X : Scheme.{u})
    [HasSheafify X.smallEtaleTopology (ModuleCat.{u} Λ1)]
    [HasSheafify X.smallEtaleTopology (ModuleCat.{u} Λ2)]
    [∀ U : X.Etale, HasWeakSheafify (X.smallEtaleTopology.over U) (ModuleCat.{u} Λ1)]
    [∀ U : X.Etale, HasWeakSheafify (X.smallEtaleTopology.over U) (ModuleCat.{u} Λ2)]
    [HasDerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ1))]
    [HasDerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ2))]
    [X.smallEtaleTopology.HasSheafCompose (ModuleCat.restrictScalars φ)] :
    (etaleDerivedRestrictScalars φ X).IsRightDerivedFunctor
      (etaleModuleRestrictScalars φ X).mapDerivedCategoryFactors.inv
      (HomologicalComplex.quasiIso
        (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ2)) (up ℤ)) :=
  sorry

/-- Postcomposition of derived extension by derived restriction remains left derived. -/
instance etaleDerivedExtendRestrict_isLeftDerived (X : Scheme.{u})
    [HasSheafify X.smallEtaleTopology (ModuleCat.{u} Λ1)]
    [HasSheafify X.smallEtaleTopology (ModuleCat.{u} Λ2)]
    [∀ U : X.Etale, HasWeakSheafify (X.smallEtaleTopology.over U) (ModuleCat.{u} Λ1)]
    [∀ U : X.Etale, HasWeakSheafify (X.smallEtaleTopology.over U) (ModuleCat.{u} Λ2)]
    [HasDerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ1))]
    [HasDerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ2))]
    [X.smallEtaleTopology.HasSheafCompose (ModuleCat.restrictScalars φ)]
    [(Functor.Homotopy.toDerived (etaleModuleExtendScalars φ X)).HasLeftDerivedFunctor
      (HomotopyCategory.quasiIso
        (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ1)) (up ℤ))] :
    (etaleDerivedExtendScalars φ X ⋙ etaleDerivedRestrictScalars φ X).IsLeftDerivedFunctor
      ((Functor.associator
          (DerivedCategory.Q :
            CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ1)) ℤ ⥤
              DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ1)))
          (etaleDerivedExtendScalars φ X)
          (etaleDerivedRestrictScalars φ X)).inv ≫
        Functor.whiskerRight
          (Functor.LeftDerived.Homotopy.cochainCounit (etaleModuleExtendScalars φ X))
          (etaleDerivedRestrictScalars φ X))
      (HomologicalComplex.quasiIso
        (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ1)) (up ℤ)) :=
  sorry

/-- Postcomposition of derived restriction by derived extension remains right derived. -/
instance etaleDerivedRestrictExtend_isRightDerived (X : Scheme.{u})
    [HasSheafify X.smallEtaleTopology (ModuleCat.{u} Λ1)]
    [HasSheafify X.smallEtaleTopology (ModuleCat.{u} Λ2)]
    [∀ U : X.Etale, HasWeakSheafify (X.smallEtaleTopology.over U) (ModuleCat.{u} Λ1)]
    [∀ U : X.Etale, HasWeakSheafify (X.smallEtaleTopology.over U) (ModuleCat.{u} Λ2)]
    [HasDerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ1))]
    [HasDerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ2))]
    [X.smallEtaleTopology.HasSheafCompose (ModuleCat.restrictScalars φ)]
    [(Functor.Homotopy.toDerived (etaleModuleExtendScalars φ X)).HasLeftDerivedFunctor
      (HomotopyCategory.quasiIso
        (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ1)) (up ℤ))] :
    (etaleDerivedRestrictScalars φ X ⋙ etaleDerivedExtendScalars φ X).IsRightDerivedFunctor
      (Functor.whiskerRight
          (etaleModuleRestrictScalars φ X).mapDerivedCategoryFactors.inv
          (etaleDerivedExtendScalars φ X) ≫
        (Functor.associator
          (DerivedCategory.Q :
            CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ2)) ℤ ⥤
              DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ2)))
          (etaleDerivedRestrictScalars φ X)
          (etaleDerivedExtendScalars φ X)).hom)
      (HomologicalComplex.quasiIso
        (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ2)) (up ℤ)) :=
  sorry

/-- Derived extension of scalars is left adjoint to derived restriction of scalars. -/
def etaleDerivedExtendRestrictAdjunction (X : Scheme.{u})
    [HasSheafify X.smallEtaleTopology (ModuleCat.{u} Λ1)]
    [HasSheafify X.smallEtaleTopology (ModuleCat.{u} Λ2)]
    [∀ U : X.Etale, HasWeakSheafify (X.smallEtaleTopology.over U) (ModuleCat.{u} Λ1)]
    [∀ U : X.Etale, HasWeakSheafify (X.smallEtaleTopology.over U) (ModuleCat.{u} Λ2)]
    [HasDerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ1))]
    [HasDerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ2))]
    [X.smallEtaleTopology.HasSheafCompose (ModuleCat.restrictScalars φ)]
    [(Functor.Homotopy.toDerived (etaleModuleExtendScalars φ X)).HasLeftDerivedFunctor
      (HomotopyCategory.quasiIso
        (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ1)) (up ℤ))] :
    etaleDerivedExtendScalars φ X ⊣ etaleDerivedRestrictScalars φ X :=
  @Adjunction.derived _ _ _ _ _ _ _ _ _ _
    (Adjunction.mapHomologicalComplexAdjunction
      (etaleModuleExtendRestrictAdjunction φ X) (up ℤ))
    (DerivedCategory.Q :
      CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ1)) ℤ ⥤
        DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ1)))
    (DerivedCategory.Q :
      CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ2)) ℤ ⥤
        DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ2)))
    (HomologicalComplex.quasiIso
      (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ1)) (up ℤ))
    (HomologicalComplex.quasiIso
      (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ2)) (up ℤ))
    inferInstance inferInstance
    (etaleDerivedExtendScalars φ X) (etaleDerivedRestrictScalars φ X)
    (Functor.LeftDerived.Homotopy.cochainCounit (etaleModuleExtendScalars φ X))
    (etaleModuleRestrictScalars φ X).mapDerivedCategoryFactors.inv
    (etaleDerivedExtendScalars_isLeftDerived φ X)
    (etaleDerivedRestrictScalars_isRightDerived φ X)
    (etaleDerivedExtendRestrict_isLeftDerived φ X)
    (etaleDerivedRestrictExtend_isRightDerived φ X)

/-- The constant étale sheaf of `Λ2`, regarded as a sheaf of `Λ1`-modules via `φ`. -/
def etaleConstantRestrictScalars (X : Scheme.{u}) :
    Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ1) :=
  (constantSheaf X.smallEtaleTopology (ModuleCat.{u} Λ1)).obj
    ((ModuleCat.restrictScalars φ).obj (ModuleCat.of Λ2 Λ2))

/-- `etaleConstantRestrictScalars` is the constant sheaf on the restriction of scalars of
`Λ2` as a module over itself. -/
theorem etaleConstantRestrictScalars_obj (X : Scheme.{u}) :
    etaleConstantRestrictScalars φ X =
      (constantSheaf X.smallEtaleTopology (ModuleCat.{u} Λ1)).obj
        ((ModuleCat.restrictScalars φ).obj (ModuleCat.of Λ2 Λ2)) :=
  sorry

/-- An isomorphism of exact additive functors induces an isomorphism of the induced
functors on derived categories. -/
def mapDerivedCategoryIso
    {A : Type v} {B : Type w} [Category.{u} A] [Category.{u} B]
    [Abelian A] [Abelian B] [HasDerivedCategory A] [HasDerivedCategory B]
    {F G : A ⥤ B} [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] (e : F ≅ G) :
    F.mapDerivedCategory ≅ G.mapDerivedCategory where
  hom :=
    ExactFunctor.MapDerivedCategory.map
      (ObjectProperty.homMk e.hom : ExactFunctor.of F ⟶ ExactFunctor.of G)
  inv :=
    ExactFunctor.MapDerivedCategory.map
      (ObjectProperty.homMk e.inv : ExactFunctor.of G ⟶ ExactFunctor.of F)
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The forward map of `mapDerivedCategoryIso` is the derived image of `e.hom`. -/
theorem mapDerivedCategoryIso_hom
    {A : Type v} {B : Type w} [Category.{u} A] [Category.{u} B]
    [Abelian A] [Abelian B] [HasDerivedCategory A] [HasDerivedCategory B]
    {F G : A ⥤ B} [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] (e : F ≅ G) :
    (mapDerivedCategoryIso e).hom =
      ExactFunctor.MapDerivedCategory.map
        (ObjectProperty.homMk e.hom : ExactFunctor.of F ⟶ ExactFunctor.of G) :=
  sorry

/-- Continuous small-étale pushforward commutes with restriction of scalars. -/
def etaleModuleRestrictScalars_pushforwardIso {X Y : Scheme.{u}} (f : X ⟶ Y)
    [X.smallEtaleTopology.HasSheafCompose (ModuleCat.restrictScalars φ)]
    [Y.smallEtaleTopology.HasSheafCompose (ModuleCat.restrictScalars φ)] :
    (smallEtalePullback f).sheafPushforwardContinuous (ModuleCat.{u} Λ2)
        Y.smallEtaleTopology X.smallEtaleTopology ⋙
      etaleModuleRestrictScalars φ Y ≅
      etaleModuleRestrictScalars φ X ⋙
        (smallEtalePullback f).sheafPushforwardContinuous (ModuleCat.{u} Λ1)
          Y.smallEtaleTopology X.smallEtaleTopology :=
  NatIso.ofComponents
    (fun G =>
      { hom :=
          ObjectProperty.homMk
            (Functor.associator (smallEtalePullback f).op G.obj
              (ModuleCat.restrictScalars φ)).hom
        inv :=
          ObjectProperty.homMk
            (Functor.associator (smallEtalePullback f).op G.obj
              (ModuleCat.restrictScalars φ)).inv
        hom_inv_id := sorry
        inv_hom_id := sorry })
    (fun _ => sorry)

/-- Evaluating the underived pushforward comparison on a sheaf is the sheaf-level
preimage of the whiskering associator. -/
theorem etaleModuleRestrictScalars_pushforwardIso_hom_app {X Y : Scheme.{u}}
    (f : X ⟶ Y)
    [X.smallEtaleTopology.HasSheafCompose (ModuleCat.restrictScalars φ)]
    [Y.smallEtaleTopology.HasSheafCompose (ModuleCat.restrictScalars φ)]
    (G : Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ2)) :
    (etaleModuleRestrictScalars_pushforwardIso φ f).hom.app G =
      ObjectProperty.homMk
        (Functor.associator (smallEtalePullback f).op G.obj
          (ModuleCat.restrictScalars φ)).hom :=
  sorry

/-- Étale extension by zero commutes with restriction of scalars. -/
def etaleModuleRestrictScalars_extensionByZeroIso {U X : Scheme.{u}} (j : U ⟶ X)
    [Etale j]
    [∀ F : U.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ1, (etaleRestriction j).op.HasLeftKanExtension F]
    [∀ F : U.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ2, (etaleRestriction j).op.HasLeftKanExtension F]
    [(ModuleCat.restrictScalars φ).PreservesLeftKanExtensions (etaleRestriction j).op]
    [HasWeakSheafify X.smallEtaleTopology (ModuleCat.{u} Λ1)]
    [HasWeakSheafify X.smallEtaleTopology (ModuleCat.{u} Λ2)]
    [U.smallEtaleTopology.HasSheafCompose (ModuleCat.restrictScalars φ)]
    [X.smallEtaleTopology.HasSheafCompose (ModuleCat.restrictScalars φ)]
    [X.smallEtaleTopology.PreservesSheafification (ModuleCat.restrictScalars φ)] :
    etaleExtensionByZero j (ModuleCat.{u} Λ2) ⋙ etaleModuleRestrictScalars φ X ≅
      etaleModuleRestrictScalars φ U ⋙ etaleExtensionByZero j (ModuleCat.{u} Λ1) :=
  Functor.sheafPullback.compSheafComposeIso (etaleRestriction j)
    (ModuleCat.restrictScalars φ) U.smallEtaleTopology X.smallEtaleTopology

/-- The extension-by-zero comparison is `sheafPullback.compSheafComposeIso` of
`ModuleCat.restrictScalars`. -/
theorem etaleModuleRestrictScalars_extensionByZeroIso_eq {U X : Scheme.{u}}
    (j : U ⟶ X) [Etale j]
    [∀ F : U.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ1, (etaleRestriction j).op.HasLeftKanExtension F]
    [∀ F : U.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ2, (etaleRestriction j).op.HasLeftKanExtension F]
    [(ModuleCat.restrictScalars φ).PreservesLeftKanExtensions (etaleRestriction j).op]
    [HasWeakSheafify X.smallEtaleTopology (ModuleCat.{u} Λ1)]
    [HasWeakSheafify X.smallEtaleTopology (ModuleCat.{u} Λ2)]
    [U.smallEtaleTopology.HasSheafCompose (ModuleCat.restrictScalars φ)]
    [X.smallEtaleTopology.HasSheafCompose (ModuleCat.restrictScalars φ)]
    [X.smallEtaleTopology.PreservesSheafification (ModuleCat.restrictScalars φ)] :
    etaleModuleRestrictScalars_extensionByZeroIso φ j =
      Functor.sheafPullback.compSheafComposeIso (etaleRestriction j)
        (ModuleCat.restrictScalars φ) U.smallEtaleTopology X.smallEtaleTopology :=
  sorry

/-- Derived extension by zero commutes with derived restriction of scalars. -/
def etaleDerivedRestrictScalars_extensionByZeroIso {U X : Scheme.{u}} (j : U ⟶ X)
    [Etale j]
    [HasSheafify U.smallEtaleTopology (ModuleCat.{u} Λ1)]
    [HasSheafify U.smallEtaleTopology (ModuleCat.{u} Λ2)]
    [HasSheafify X.smallEtaleTopology (ModuleCat.{u} Λ1)]
    [HasSheafify X.smallEtaleTopology (ModuleCat.{u} Λ2)]
    [∀ V : U.Etale, HasWeakSheafify (U.smallEtaleTopology.over V) (ModuleCat.{u} Λ1)]
    [∀ V : U.Etale, HasWeakSheafify (U.smallEtaleTopology.over V) (ModuleCat.{u} Λ2)]
    [∀ V : X.Etale, HasWeakSheafify (X.smallEtaleTopology.over V) (ModuleCat.{u} Λ1)]
    [∀ V : X.Etale, HasWeakSheafify (X.smallEtaleTopology.over V) (ModuleCat.{u} Λ2)]
    [HasDerivedCategory (Sheaf U.smallEtaleTopology (ModuleCat.{u} Λ1))]
    [HasDerivedCategory (Sheaf U.smallEtaleTopology (ModuleCat.{u} Λ2))]
    [HasDerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ1))]
    [HasDerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ2))]
    [∀ F : U.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ1, (etaleRestriction j).op.HasLeftKanExtension F]
    [∀ F : U.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ2, (etaleRestriction j).op.HasLeftKanExtension F]
    [(ModuleCat.restrictScalars φ).PreservesLeftKanExtensions (etaleRestriction j).op]
    [U.smallEtaleTopology.HasSheafCompose (ModuleCat.restrictScalars φ)]
    [X.smallEtaleTopology.HasSheafCompose (ModuleCat.restrictScalars φ)]
    [X.smallEtaleTopology.PreservesSheafification (ModuleCat.restrictScalars φ)]
    [(etaleExtensionByZero j (ModuleCat.{u} Λ1)).Additive]
    [(etaleExtensionByZero j (ModuleCat.{u} Λ2)).Additive]
    [PreservesFiniteLimits (etaleExtensionByZero j (ModuleCat.{u} Λ1))]
    [PreservesFiniteColimits (etaleExtensionByZero j (ModuleCat.{u} Λ1))]
    [PreservesFiniteLimits (etaleExtensionByZero j (ModuleCat.{u} Λ2))]
    [PreservesFiniteColimits (etaleExtensionByZero j (ModuleCat.{u} Λ2))] :
    (etaleExtensionByZero j (ModuleCat.{u} Λ2)).mapDerivedCategory ⋙
        etaleDerivedRestrictScalars φ X ≅
      etaleDerivedRestrictScalars φ U ⋙
        (etaleExtensionByZero j (ModuleCat.{u} Λ1)).mapDerivedCategory :=
  (ExactFunctor.MapDerivedCategory.compFunctorIso
      (ExactFunctor.of (etaleExtensionByZero j (ModuleCat.{u} Λ2)))
      (ExactFunctor.of (etaleModuleRestrictScalars φ X))).symm ≪≫
    mapDerivedCategoryIso (etaleModuleRestrictScalars_extensionByZeroIso φ j) ≪≫
    ExactFunctor.MapDerivedCategory.compFunctorIso
      (ExactFunctor.of (etaleModuleRestrictScalars φ U))
      (ExactFunctor.of (etaleExtensionByZero j (ModuleCat.{u} Λ1)))

/-- Cochain identification of `toDerived (push ⋙ res)` with iterated application of
pushforward on complexes and derived restriction of scalars. -/
def etaleDerivedRestrictScalars_pushforwardToIteratedIso {X Y : Scheme.{u}}
    (f : X ⟶ Y)
    [HasSheafify X.smallEtaleTopology (ModuleCat.{u} Λ1)]
    [HasSheafify X.smallEtaleTopology (ModuleCat.{u} Λ2)]
    [HasSheafify Y.smallEtaleTopology (ModuleCat.{u} Λ1)]
    [HasSheafify Y.smallEtaleTopology (ModuleCat.{u} Λ2)]
    [∀ U : X.Etale, HasWeakSheafify (X.smallEtaleTopology.over U) (ModuleCat.{u} Λ1)]
    [∀ U : X.Etale, HasWeakSheafify (X.smallEtaleTopology.over U) (ModuleCat.{u} Λ2)]
    [∀ U : Y.Etale, HasWeakSheafify (Y.smallEtaleTopology.over U) (ModuleCat.{u} Λ1)]
    [∀ U : Y.Etale, HasWeakSheafify (Y.smallEtaleTopology.over U) (ModuleCat.{u} Λ2)]
    [HasDerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ1))]
    [HasDerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ2))]
    [HasDerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ1))]
    [HasDerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ2))]
    [X.smallEtaleTopology.HasSheafCompose (ModuleCat.restrictScalars φ)]
    [Y.smallEtaleTopology.HasSheafCompose (ModuleCat.restrictScalars φ)]
    [((smallEtalePullback f).sheafPushforwardContinuous
        (ModuleCat.{u} Λ2) Y.smallEtaleTopology X.smallEtaleTopology).Additive] :
    RightDerived.Cochain.toDerived
        ((smallEtalePullback f).sheafPushforwardContinuous (ModuleCat.{u} Λ2) Y.smallEtaleTopology X.smallEtaleTopology ⋙ etaleModuleRestrictScalars φ Y) ≅
      ((smallEtalePullback f).sheafPushforwardContinuous (ModuleCat.{u} Λ2) Y.smallEtaleTopology X.smallEtaleTopology).mapHomologicalComplex (up ℤ) ⋙
        DerivedCategory.Q ⋙ etaleDerivedRestrictScalars φ Y :=
  Functor.isoWhiskerRight
      (Functor.mapHomologicalComplexCompIso
        (Iso.refl ((smallEtalePullback f).sheafPushforwardContinuous (ModuleCat.{u} Λ2) Y.smallEtaleTopology X.smallEtaleTopology ⋙ etaleModuleRestrictScalars φ Y))
        (up ℤ)).symm
      (DerivedCategory.Q :
        CochainComplex (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ1)) ℤ ⥤
          EtaleDerived Y Λ1) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft
      (((smallEtalePullback f).sheafPushforwardContinuous (ModuleCat.{u} Λ2) Y.smallEtaleTopology X.smallEtaleTopology).mapHomologicalComplex (up ℤ))
      (etaleModuleRestrictScalars φ Y).mapDerivedCategoryFactors.symm ≪≫
    (Functor.associator _ _ _).symm

/-- The cochain-level unit presenting `R f_* ⋙ res` as a right-derived model of
`f_* ⋙ res`. -/
def etaleDerivedRestrictScalars_pushforwardUnit {X Y : Scheme.{u}} (f : X ⟶ Y)
    [HasSheafify X.smallEtaleTopology (ModuleCat.{u} Λ1)]
    [HasSheafify X.smallEtaleTopology (ModuleCat.{u} Λ2)]
    [HasSheafify Y.smallEtaleTopology (ModuleCat.{u} Λ1)]
    [HasSheafify Y.smallEtaleTopology (ModuleCat.{u} Λ2)]
    [∀ U : X.Etale, HasWeakSheafify (X.smallEtaleTopology.over U) (ModuleCat.{u} Λ1)]
    [∀ U : X.Etale, HasWeakSheafify (X.smallEtaleTopology.over U) (ModuleCat.{u} Λ2)]
    [∀ U : Y.Etale, HasWeakSheafify (Y.smallEtaleTopology.over U) (ModuleCat.{u} Λ1)]
    [∀ U : Y.Etale, HasWeakSheafify (Y.smallEtaleTopology.over U) (ModuleCat.{u} Λ2)]
    [HasDerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ1))]
    [HasDerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ2))]
    [HasDerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ1))]
    [HasDerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ2))]
    [X.smallEtaleTopology.HasSheafCompose (ModuleCat.restrictScalars φ)]
    [Y.smallEtaleTopology.HasSheafCompose (ModuleCat.restrictScalars φ)]
    [((smallEtalePullback f).sheafPushforwardContinuous
        (ModuleCat.{u} Λ2) Y.smallEtaleTopology X.smallEtaleTopology).Additive]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived
        ((smallEtalePullback f).sheafPushforwardContinuous
          (ModuleCat.{u} Λ2) Y.smallEtaleTopology X.smallEtaleTopology))
      (HomologicalComplex.quasiIso
        (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ2)) (up ℤ))] :
    RightDerived.Cochain.toDerived
        ((smallEtalePullback f).sheafPushforwardContinuous (ModuleCat.{u} Λ2) Y.smallEtaleTopology X.smallEtaleTopology ⋙ etaleModuleRestrictScalars φ Y) ⟶
      DerivedCategory.Q ⋙
        (etaleDerivedPushforward f ⋙ etaleDerivedRestrictScalars φ Y) :=
  (etaleDerivedRestrictScalars_pushforwardToIteratedIso φ f).hom ≫
    Functor.whiskerRight (RightDerived.Cochain.unit ((smallEtalePullback f).sheafPushforwardContinuous (ModuleCat.{u} Λ2) Y.smallEtaleTopology X.smallEtaleTopology))
      (etaleDerivedRestrictScalars φ Y) ≫
    (Functor.associator _ _ _).hom

/-- `R f_* ⋙ res` is a right-derived functor of `f_* ⋙ res`. -/
instance etaleDerivedRestrictScalars_pushforward_isRightDerived {X Y : Scheme.{u}}
    (f : X ⟶ Y)
    [HasSheafify X.smallEtaleTopology (ModuleCat.{u} Λ1)]
    [HasSheafify X.smallEtaleTopology (ModuleCat.{u} Λ2)]
    [HasSheafify Y.smallEtaleTopology (ModuleCat.{u} Λ1)]
    [HasSheafify Y.smallEtaleTopology (ModuleCat.{u} Λ2)]
    [∀ U : X.Etale, HasWeakSheafify (X.smallEtaleTopology.over U) (ModuleCat.{u} Λ1)]
    [∀ U : X.Etale, HasWeakSheafify (X.smallEtaleTopology.over U) (ModuleCat.{u} Λ2)]
    [∀ U : Y.Etale, HasWeakSheafify (Y.smallEtaleTopology.over U) (ModuleCat.{u} Λ1)]
    [∀ U : Y.Etale, HasWeakSheafify (Y.smallEtaleTopology.over U) (ModuleCat.{u} Λ2)]
    [HasDerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ1))]
    [HasDerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ2))]
    [HasDerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ1))]
    [HasDerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ2))]
    [X.smallEtaleTopology.HasSheafCompose (ModuleCat.restrictScalars φ)]
    [Y.smallEtaleTopology.HasSheafCompose (ModuleCat.restrictScalars φ)]
    [((smallEtalePullback f).sheafPushforwardContinuous
        (ModuleCat.{u} Λ2) Y.smallEtaleTopology X.smallEtaleTopology).Additive]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived
        ((smallEtalePullback f).sheafPushforwardContinuous
          (ModuleCat.{u} Λ2) Y.smallEtaleTopology X.smallEtaleTopology))
      (HomologicalComplex.quasiIso
        (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ2)) (up ℤ))] :
    (etaleDerivedPushforward f ⋙ etaleDerivedRestrictScalars φ Y).IsRightDerivedFunctor
      (etaleDerivedRestrictScalars_pushforwardUnit φ f)
      (HomologicalComplex.quasiIso
        (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ2)) (up ℤ)) :=
  sorry

/-- `res ⋙ R f_*` is a right-derived functor of `res ⋙ f_*`. -/
instance etaleDerivedRestrictScalars_pushforward_exactFirst_isRightDerived
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [HasSheafify X.smallEtaleTopology (ModuleCat.{u} Λ1)]
    [HasSheafify X.smallEtaleTopology (ModuleCat.{u} Λ2)]
    [HasSheafify Y.smallEtaleTopology (ModuleCat.{u} Λ1)]
    [HasSheafify Y.smallEtaleTopology (ModuleCat.{u} Λ2)]
    [∀ U : X.Etale, HasWeakSheafify (X.smallEtaleTopology.over U) (ModuleCat.{u} Λ1)]
    [∀ U : X.Etale, HasWeakSheafify (X.smallEtaleTopology.over U) (ModuleCat.{u} Λ2)]
    [∀ U : Y.Etale, HasWeakSheafify (Y.smallEtaleTopology.over U) (ModuleCat.{u} Λ1)]
    [∀ U : Y.Etale, HasWeakSheafify (Y.smallEtaleTopology.over U) (ModuleCat.{u} Λ2)]
    [HasDerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ1))]
    [HasDerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ2))]
    [HasDerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ1))]
    [HasDerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ2))]
    [X.smallEtaleTopology.HasSheafCompose (ModuleCat.restrictScalars φ)]
    [Y.smallEtaleTopology.HasSheafCompose (ModuleCat.restrictScalars φ)]
    [((smallEtalePullback f).sheafPushforwardContinuous
        (ModuleCat.{u} Λ1) Y.smallEtaleTopology X.smallEtaleTopology).Additive]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived
        ((smallEtalePullback f).sheafPushforwardContinuous
          (ModuleCat.{u} Λ1) Y.smallEtaleTopology X.smallEtaleTopology))
      (HomologicalComplex.quasiIso
        (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ1)) (up ℤ))] :
    (etaleDerivedRestrictScalars φ X ⋙ etaleDerivedPushforward f).IsRightDerivedFunctor
      (RightDerived.Cochain.ExactFirst.unit
        (ExactFunctor.of (etaleModuleRestrictScalars φ X))
        ((smallEtalePullback f).sheafPushforwardContinuous (ModuleCat.{u} Λ1) Y.smallEtaleTopology X.smallEtaleTopology))
      (HomologicalComplex.quasiIso
        (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ2)) (up ℤ)) :=
  sorry

/-- Derived small-étale pushforward commutes with restriction of scalars. -/
def etaleDerivedRestrictScalars_pushforwardIso {X Y : Scheme.{u}} (f : X ⟶ Y)
    [HasSheafify X.smallEtaleTopology (ModuleCat.{u} Λ1)]
    [HasSheafify X.smallEtaleTopology (ModuleCat.{u} Λ2)]
    [HasSheafify Y.smallEtaleTopology (ModuleCat.{u} Λ1)]
    [HasSheafify Y.smallEtaleTopology (ModuleCat.{u} Λ2)]
    [∀ U : X.Etale, HasWeakSheafify (X.smallEtaleTopology.over U) (ModuleCat.{u} Λ1)]
    [∀ U : X.Etale, HasWeakSheafify (X.smallEtaleTopology.over U) (ModuleCat.{u} Λ2)]
    [∀ U : Y.Etale, HasWeakSheafify (Y.smallEtaleTopology.over U) (ModuleCat.{u} Λ1)]
    [∀ U : Y.Etale, HasWeakSheafify (Y.smallEtaleTopology.over U) (ModuleCat.{u} Λ2)]
    [HasDerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ1))]
    [HasDerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ2))]
    [HasDerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ1))]
    [HasDerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ2))]
    [X.smallEtaleTopology.HasSheafCompose (ModuleCat.restrictScalars φ)]
    [Y.smallEtaleTopology.HasSheafCompose (ModuleCat.restrictScalars φ)]
    [((smallEtalePullback f).sheafPushforwardContinuous
        (ModuleCat.{u} Λ1) Y.smallEtaleTopology X.smallEtaleTopology).Additive]
    [((smallEtalePullback f).sheafPushforwardContinuous
        (ModuleCat.{u} Λ2) Y.smallEtaleTopology X.smallEtaleTopology).Additive]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived
        ((smallEtalePullback f).sheafPushforwardContinuous
          (ModuleCat.{u} Λ1) Y.smallEtaleTopology X.smallEtaleTopology))
      (HomologicalComplex.quasiIso
        (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ1)) (up ℤ))]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived
        ((smallEtalePullback f).sheafPushforwardContinuous
          (ModuleCat.{u} Λ2) Y.smallEtaleTopology X.smallEtaleTopology))
      (HomologicalComplex.quasiIso
        (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ2)) (up ℤ))] :
    etaleDerivedPushforward f ⋙ etaleDerivedRestrictScalars φ Y ≅
      etaleDerivedRestrictScalars φ X ⋙ etaleDerivedPushforward f :=
  RightDerived.natIsoOfIso
    (DerivedCategory.Q :
      CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ2)) ℤ ⥤
        EtaleDerived X Λ2)
    (HomologicalComplex.quasiIso
      (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ2)) (up ℤ))
    (etaleDerivedRestrictScalars_pushforwardUnit φ f)
    (RightDerived.Cochain.ExactFirst.unit
      (ExactFunctor.of (etaleModuleRestrictScalars φ X))
      ((smallEtalePullback f).sheafPushforwardContinuous (ModuleCat.{u} Λ1) Y.smallEtaleTopology X.smallEtaleTopology))
    (Functor.isoWhiskerRight
      (NatIso.mapHomologicalComplex
        (etaleModuleRestrictScalars_pushforwardIso φ f) (up ℤ))
      (DerivedCategory.Q :
        CochainComplex (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ1)) ℤ ⥤
          EtaleDerived Y Λ1))

/-- The component of the derived pushforward comparison at an object of
`D(X_étale, Λ2)`. -/
def etaleDerivedRestrictScalars_pushforwardIso_hom_app {X Y : Scheme.{u}}
    (f : X ⟶ Y)
    [HasSheafify X.smallEtaleTopology (ModuleCat.{u} Λ1)]
    [HasSheafify X.smallEtaleTopology (ModuleCat.{u} Λ2)]
    [HasSheafify Y.smallEtaleTopology (ModuleCat.{u} Λ1)]
    [HasSheafify Y.smallEtaleTopology (ModuleCat.{u} Λ2)]
    [∀ U : X.Etale, HasWeakSheafify (X.smallEtaleTopology.over U) (ModuleCat.{u} Λ1)]
    [∀ U : X.Etale, HasWeakSheafify (X.smallEtaleTopology.over U) (ModuleCat.{u} Λ2)]
    [∀ U : Y.Etale, HasWeakSheafify (Y.smallEtaleTopology.over U) (ModuleCat.{u} Λ1)]
    [∀ U : Y.Etale, HasWeakSheafify (Y.smallEtaleTopology.over U) (ModuleCat.{u} Λ2)]
    [HasDerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ1))]
    [HasDerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ2))]
    [HasDerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ1))]
    [HasDerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ2))]
    [X.smallEtaleTopology.HasSheafCompose (ModuleCat.restrictScalars φ)]
    [Y.smallEtaleTopology.HasSheafCompose (ModuleCat.restrictScalars φ)]
    [((smallEtalePullback f).sheafPushforwardContinuous
        (ModuleCat.{u} Λ1) Y.smallEtaleTopology X.smallEtaleTopology).Additive]
    [((smallEtalePullback f).sheafPushforwardContinuous
        (ModuleCat.{u} Λ2) Y.smallEtaleTopology X.smallEtaleTopology).Additive]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived
        ((smallEtalePullback f).sheafPushforwardContinuous
          (ModuleCat.{u} Λ1) Y.smallEtaleTopology X.smallEtaleTopology))
      (HomologicalComplex.quasiIso
        (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ1)) (up ℤ))]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived
        ((smallEtalePullback f).sheafPushforwardContinuous
          (ModuleCat.{u} Λ2) Y.smallEtaleTopology X.smallEtaleTopology))
      (HomologicalComplex.quasiIso
        (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ2)) (up ℤ))]
    (K : EtaleDerived X Λ2) :
    (etaleDerivedRestrictScalars φ Y).obj ((etaleDerivedPushforward f).obj K) ≅
      (etaleDerivedPushforward f).obj ((etaleDerivedRestrictScalars φ X).obj K) :=
  (etaleDerivedRestrictScalars_pushforwardIso φ f).app K

/-- The mate of the restriction-of-scalars pushforward comparison along
derived extension ⊣ derived restriction is an isomorphism. -/
instance etaleDerivedExtendScalars_pushforwardIso_isIso {X Y : Scheme.{u}}
    (f : X ⟶ Y)
    [HasSheafify X.smallEtaleTopology (ModuleCat.{u} Λ1)]
    [HasSheafify X.smallEtaleTopology (ModuleCat.{u} Λ2)]
    [HasSheafify Y.smallEtaleTopology (ModuleCat.{u} Λ1)]
    [HasSheafify Y.smallEtaleTopology (ModuleCat.{u} Λ2)]
    [∀ U : X.Etale, HasWeakSheafify (X.smallEtaleTopology.over U) (ModuleCat.{u} Λ1)]
    [∀ U : X.Etale, HasWeakSheafify (X.smallEtaleTopology.over U) (ModuleCat.{u} Λ2)]
    [∀ U : Y.Etale, HasWeakSheafify (Y.smallEtaleTopology.over U) (ModuleCat.{u} Λ1)]
    [∀ U : Y.Etale, HasWeakSheafify (Y.smallEtaleTopology.over U) (ModuleCat.{u} Λ2)]
    [HasDerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ1))]
    [HasDerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ2))]
    [HasDerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ1))]
    [HasDerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ2))]
    [X.smallEtaleTopology.HasSheafCompose (ModuleCat.restrictScalars φ)]
    [Y.smallEtaleTopology.HasSheafCompose (ModuleCat.restrictScalars φ)]
    [((smallEtalePullback f).sheafPushforwardContinuous
        (ModuleCat.{u} Λ1) Y.smallEtaleTopology X.smallEtaleTopology).Additive]
    [((smallEtalePullback f).sheafPushforwardContinuous
        (ModuleCat.{u} Λ2) Y.smallEtaleTopology X.smallEtaleTopology).Additive]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived
        ((smallEtalePullback f).sheafPushforwardContinuous
          (ModuleCat.{u} Λ1) Y.smallEtaleTopology X.smallEtaleTopology))
      (HomologicalComplex.quasiIso
        (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ1)) (up ℤ))]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived
        ((smallEtalePullback f).sheafPushforwardContinuous
          (ModuleCat.{u} Λ2) Y.smallEtaleTopology X.smallEtaleTopology))
      (HomologicalComplex.quasiIso
        (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ2)) (up ℤ))]
    [(Functor.Homotopy.toDerived (etaleModuleExtendScalars φ X)).HasLeftDerivedFunctor
      (HomotopyCategory.quasiIso
        (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ1)) (up ℤ))]
    [(Functor.Homotopy.toDerived (etaleModuleExtendScalars φ Y)).HasLeftDerivedFunctor
      (HomotopyCategory.quasiIso
        (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ1)) (up ℤ))] :
    IsIso
      ((mateEquiv
          (etaleDerivedExtendRestrictAdjunction φ X)
          (etaleDerivedExtendRestrictAdjunction φ Y)).symm
        (etaleDerivedRestrictScalars_pushforwardIso φ f).inv) :=
  sorry

/-- Derived pushforward commutes with derived extension of scalars. -/
def etaleDerivedExtendScalars_pushforwardIso {X Y : Scheme.{u}} (f : X ⟶ Y)
    [HasSheafify X.smallEtaleTopology (ModuleCat.{u} Λ1)]
    [HasSheafify X.smallEtaleTopology (ModuleCat.{u} Λ2)]
    [HasSheafify Y.smallEtaleTopology (ModuleCat.{u} Λ1)]
    [HasSheafify Y.smallEtaleTopology (ModuleCat.{u} Λ2)]
    [∀ U : X.Etale, HasWeakSheafify (X.smallEtaleTopology.over U) (ModuleCat.{u} Λ1)]
    [∀ U : X.Etale, HasWeakSheafify (X.smallEtaleTopology.over U) (ModuleCat.{u} Λ2)]
    [∀ U : Y.Etale, HasWeakSheafify (Y.smallEtaleTopology.over U) (ModuleCat.{u} Λ1)]
    [∀ U : Y.Etale, HasWeakSheafify (Y.smallEtaleTopology.over U) (ModuleCat.{u} Λ2)]
    [HasDerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ1))]
    [HasDerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ2))]
    [HasDerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ1))]
    [HasDerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ2))]
    [X.smallEtaleTopology.HasSheafCompose (ModuleCat.restrictScalars φ)]
    [Y.smallEtaleTopology.HasSheafCompose (ModuleCat.restrictScalars φ)]
    [((smallEtalePullback f).sheafPushforwardContinuous
        (ModuleCat.{u} Λ1) Y.smallEtaleTopology X.smallEtaleTopology).Additive]
    [((smallEtalePullback f).sheafPushforwardContinuous
        (ModuleCat.{u} Λ2) Y.smallEtaleTopology X.smallEtaleTopology).Additive]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived
        ((smallEtalePullback f).sheafPushforwardContinuous
          (ModuleCat.{u} Λ1) Y.smallEtaleTopology X.smallEtaleTopology))
      (HomologicalComplex.quasiIso
        (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ1)) (up ℤ))]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived
        ((smallEtalePullback f).sheafPushforwardContinuous
          (ModuleCat.{u} Λ2) Y.smallEtaleTopology X.smallEtaleTopology))
      (HomologicalComplex.quasiIso
        (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ2)) (up ℤ))]
    [(Functor.Homotopy.toDerived (etaleModuleExtendScalars φ X)).HasLeftDerivedFunctor
      (HomotopyCategory.quasiIso
        (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ1)) (up ℤ))]
    [(Functor.Homotopy.toDerived (etaleModuleExtendScalars φ Y)).HasLeftDerivedFunctor
      (HomotopyCategory.quasiIso
        (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ1)) (up ℤ))] :
    etaleDerivedPushforward f ⋙ etaleDerivedExtendScalars φ Y ≅
      etaleDerivedExtendScalars φ X ⋙ etaleDerivedPushforward f :=
  asIso
    ((mateEquiv
        (etaleDerivedExtendRestrictAdjunction φ X)
        (etaleDerivedExtendRestrictAdjunction φ Y)).symm
      (etaleDerivedRestrictScalars_pushforwardIso φ f).inv)

/-- The component of the derived pushforward/extension-of-scalars comparison. -/
def etaleDerivedExtendScalars_pushforwardIso_hom_app {X Y : Scheme.{u}}
    (f : X ⟶ Y)
    [HasSheafify X.smallEtaleTopology (ModuleCat.{u} Λ1)]
    [HasSheafify X.smallEtaleTopology (ModuleCat.{u} Λ2)]
    [HasSheafify Y.smallEtaleTopology (ModuleCat.{u} Λ1)]
    [HasSheafify Y.smallEtaleTopology (ModuleCat.{u} Λ2)]
    [∀ U : X.Etale, HasWeakSheafify (X.smallEtaleTopology.over U) (ModuleCat.{u} Λ1)]
    [∀ U : X.Etale, HasWeakSheafify (X.smallEtaleTopology.over U) (ModuleCat.{u} Λ2)]
    [∀ U : Y.Etale, HasWeakSheafify (Y.smallEtaleTopology.over U) (ModuleCat.{u} Λ1)]
    [∀ U : Y.Etale, HasWeakSheafify (Y.smallEtaleTopology.over U) (ModuleCat.{u} Λ2)]
    [HasDerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ1))]
    [HasDerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ2))]
    [HasDerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ1))]
    [HasDerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ2))]
    [X.smallEtaleTopology.HasSheafCompose (ModuleCat.restrictScalars φ)]
    [Y.smallEtaleTopology.HasSheafCompose (ModuleCat.restrictScalars φ)]
    [((smallEtalePullback f).sheafPushforwardContinuous
        (ModuleCat.{u} Λ1) Y.smallEtaleTopology X.smallEtaleTopology).Additive]
    [((smallEtalePullback f).sheafPushforwardContinuous
        (ModuleCat.{u} Λ2) Y.smallEtaleTopology X.smallEtaleTopology).Additive]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived
        ((smallEtalePullback f).sheafPushforwardContinuous
          (ModuleCat.{u} Λ1) Y.smallEtaleTopology X.smallEtaleTopology))
      (HomologicalComplex.quasiIso
        (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ1)) (up ℤ))]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived
        ((smallEtalePullback f).sheafPushforwardContinuous
          (ModuleCat.{u} Λ2) Y.smallEtaleTopology X.smallEtaleTopology))
      (HomologicalComplex.quasiIso
        (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ2)) (up ℤ))]
    [(Functor.Homotopy.toDerived (etaleModuleExtendScalars φ X)).HasLeftDerivedFunctor
      (HomotopyCategory.quasiIso
        (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ1)) (up ℤ))]
    [(Functor.Homotopy.toDerived (etaleModuleExtendScalars φ Y)).HasLeftDerivedFunctor
      (HomotopyCategory.quasiIso
        (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ1)) (up ℤ))]
    (K : EtaleDerived X Λ1) :
    (etaleDerivedExtendScalars φ Y).obj ((etaleDerivedPushforward f).obj K) ≅
      (etaleDerivedPushforward f).obj ((etaleDerivedExtendScalars φ X).obj K) :=
  (etaleDerivedExtendScalars_pushforwardIso φ f).app K

/-- The mate of the restriction-of-scalars extension-by-zero comparison along
derived extension ⊣ derived restriction is an isomorphism. -/
instance etaleDerivedExtendScalars_extensionByZeroIso_isIso {U X : Scheme.{u}}
    (j : U ⟶ X) [Etale j]
    [HasSheafify U.smallEtaleTopology (ModuleCat.{u} Λ1)]
    [HasSheafify U.smallEtaleTopology (ModuleCat.{u} Λ2)]
    [HasSheafify X.smallEtaleTopology (ModuleCat.{u} Λ1)]
    [HasSheafify X.smallEtaleTopology (ModuleCat.{u} Λ2)]
    [∀ V : U.Etale, HasWeakSheafify (U.smallEtaleTopology.over V) (ModuleCat.{u} Λ1)]
    [∀ V : U.Etale, HasWeakSheafify (U.smallEtaleTopology.over V) (ModuleCat.{u} Λ2)]
    [∀ V : X.Etale, HasWeakSheafify (X.smallEtaleTopology.over V) (ModuleCat.{u} Λ1)]
    [∀ V : X.Etale, HasWeakSheafify (X.smallEtaleTopology.over V) (ModuleCat.{u} Λ2)]
    [HasDerivedCategory (Sheaf U.smallEtaleTopology (ModuleCat.{u} Λ1))]
    [HasDerivedCategory (Sheaf U.smallEtaleTopology (ModuleCat.{u} Λ2))]
    [HasDerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ1))]
    [HasDerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ2))]
    [∀ F : U.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ1, (etaleRestriction j).op.HasLeftKanExtension F]
    [∀ F : U.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ2, (etaleRestriction j).op.HasLeftKanExtension F]
    [(ModuleCat.restrictScalars φ).PreservesLeftKanExtensions (etaleRestriction j).op]
    [U.smallEtaleTopology.HasSheafCompose (ModuleCat.restrictScalars φ)]
    [X.smallEtaleTopology.HasSheafCompose (ModuleCat.restrictScalars φ)]
    [X.smallEtaleTopology.PreservesSheafification (ModuleCat.restrictScalars φ)]
    [(etaleExtensionByZero j (ModuleCat.{u} Λ1)).Additive]
    [(etaleExtensionByZero j (ModuleCat.{u} Λ2)).Additive]
    [PreservesFiniteLimits (etaleExtensionByZero j (ModuleCat.{u} Λ1))]
    [PreservesFiniteColimits (etaleExtensionByZero j (ModuleCat.{u} Λ1))]
    [PreservesFiniteLimits (etaleExtensionByZero j (ModuleCat.{u} Λ2))]
    [PreservesFiniteColimits (etaleExtensionByZero j (ModuleCat.{u} Λ2))]
    [(Functor.Homotopy.toDerived (etaleModuleExtendScalars φ U)).HasLeftDerivedFunctor
      (HomotopyCategory.quasiIso
        (Sheaf U.smallEtaleTopology (ModuleCat.{u} Λ1)) (up ℤ))]
    [(Functor.Homotopy.toDerived (etaleModuleExtendScalars φ X)).HasLeftDerivedFunctor
      (HomotopyCategory.quasiIso
        (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ1)) (up ℤ))] :
    IsIso
      ((mateEquiv
          (etaleDerivedExtendRestrictAdjunction φ U)
          (etaleDerivedExtendRestrictAdjunction φ X)).symm
        (etaleDerivedRestrictScalars_extensionByZeroIso φ j).inv) :=
  sorry

/-- Derived extension by zero commutes with derived extension of scalars. -/
def etaleDerivedExtendScalars_extensionByZeroIso {U X : Scheme.{u}} (j : U ⟶ X)
    [Etale j]
    [HasSheafify U.smallEtaleTopology (ModuleCat.{u} Λ1)]
    [HasSheafify U.smallEtaleTopology (ModuleCat.{u} Λ2)]
    [HasSheafify X.smallEtaleTopology (ModuleCat.{u} Λ1)]
    [HasSheafify X.smallEtaleTopology (ModuleCat.{u} Λ2)]
    [∀ V : U.Etale, HasWeakSheafify (U.smallEtaleTopology.over V) (ModuleCat.{u} Λ1)]
    [∀ V : U.Etale, HasWeakSheafify (U.smallEtaleTopology.over V) (ModuleCat.{u} Λ2)]
    [∀ V : X.Etale, HasWeakSheafify (X.smallEtaleTopology.over V) (ModuleCat.{u} Λ1)]
    [∀ V : X.Etale, HasWeakSheafify (X.smallEtaleTopology.over V) (ModuleCat.{u} Λ2)]
    [HasDerivedCategory (Sheaf U.smallEtaleTopology (ModuleCat.{u} Λ1))]
    [HasDerivedCategory (Sheaf U.smallEtaleTopology (ModuleCat.{u} Λ2))]
    [HasDerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ1))]
    [HasDerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ2))]
    [∀ F : U.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ1, (etaleRestriction j).op.HasLeftKanExtension F]
    [∀ F : U.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ2, (etaleRestriction j).op.HasLeftKanExtension F]
    [(ModuleCat.restrictScalars φ).PreservesLeftKanExtensions (etaleRestriction j).op]
    [U.smallEtaleTopology.HasSheafCompose (ModuleCat.restrictScalars φ)]
    [X.smallEtaleTopology.HasSheafCompose (ModuleCat.restrictScalars φ)]
    [X.smallEtaleTopology.PreservesSheafification (ModuleCat.restrictScalars φ)]
    [(etaleExtensionByZero j (ModuleCat.{u} Λ1)).Additive]
    [(etaleExtensionByZero j (ModuleCat.{u} Λ2)).Additive]
    [PreservesFiniteLimits (etaleExtensionByZero j (ModuleCat.{u} Λ1))]
    [PreservesFiniteColimits (etaleExtensionByZero j (ModuleCat.{u} Λ1))]
    [PreservesFiniteLimits (etaleExtensionByZero j (ModuleCat.{u} Λ2))]
    [PreservesFiniteColimits (etaleExtensionByZero j (ModuleCat.{u} Λ2))]
    [(Functor.Homotopy.toDerived (etaleModuleExtendScalars φ U)).HasLeftDerivedFunctor
      (HomotopyCategory.quasiIso
        (Sheaf U.smallEtaleTopology (ModuleCat.{u} Λ1)) (up ℤ))]
    [(Functor.Homotopy.toDerived (etaleModuleExtendScalars φ X)).HasLeftDerivedFunctor
      (HomotopyCategory.quasiIso
        (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ1)) (up ℤ))] :
    (etaleExtensionByZero j (ModuleCat.{u} Λ1)).mapDerivedCategory ⋙
        etaleDerivedExtendScalars φ X ≅
      etaleDerivedExtendScalars φ U ⋙
        (etaleExtensionByZero j (ModuleCat.{u} Λ2)).mapDerivedCategory :=
  asIso
    ((mateEquiv
        (etaleDerivedExtendRestrictAdjunction φ U)
        (etaleDerivedExtendRestrictAdjunction φ X)).symm
      (etaleDerivedRestrictScalars_extensionByZeroIso φ j).inv)

/-- Restricting derived extension of scalars recovers derived tensor with the
constant sheaf of `Λ2` as a `Λ1`-module. -/
theorem etaleDerivedRestrictScalars_extendScalars (X : Scheme.{u})
    [HasSheafify X.smallEtaleTopology (ModuleCat.{u} Λ1)]
    [HasSheafify X.smallEtaleTopology (ModuleCat.{u} Λ2)]
    [∀ U : X.Etale, HasWeakSheafify (X.smallEtaleTopology.over U) (ModuleCat.{u} Λ1)]
    [∀ U : X.Etale, HasWeakSheafify (X.smallEtaleTopology.over U) (ModuleCat.{u} Λ2)]
    [HasDerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ1))]
    [HasDerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ2))]
    [X.smallEtaleTopology.HasSheafCompose (ModuleCat.restrictScalars φ)]
    [(Functor.Homotopy.toDerived (etaleModuleExtendScalars φ X)).HasLeftDerivedFunctor
      (HomotopyCategory.quasiIso
        (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ1)) (up ℤ))]
    [MonoidalCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ1))]
    [MonoidalPreadditive (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ1))]
    [∀ (K L : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ1)) ℤ),
      HomologicalComplex.HasMapBifunctor K L
        (curriedTensor (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ1))) (up ℤ)]
    [hTensor :
      @DerivedCategory.DerivedTensor.Right.Has
        (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ1)) _ _ _ _ _ _]
    (E : EtaleDerived X Λ1) :
    IsIsomorphic
      ((etaleDerivedRestrictScalars φ X).obj ((etaleDerivedExtendScalars φ X).obj E))
      (E ⊗ᴸ
        ((DerivedCategory.singleFunctor
            (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ1)) 0).obj
          (etaleConstantRestrictScalars φ X))) :=
  sorry

end AlgebraicGeometry.Scheme.Etale

end
