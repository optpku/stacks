/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Derived.UpperShriek
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.ConstantModule
public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.DerivedCategory.Linear
public import Mathlib.AlgebraicGeometry.Sites.AffineEtale
public import Mathlib.CategoryTheory.Shift.Adjunction
public import Mathlib.GroupTheory.Torsion

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
open CategoryTheory.Linear CategoryTheory.Sheaf
open AlgebraicGeometry AlgebraicGeometry.Scheme Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

variable (Λ : Type u) [CommRing Λ]
variable [∀ U : Scheme.{u}, HasWeakSheafify U.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [∀ (U V : Scheme.{u}) (f : U ⟶ V) [Etale f]
    (F : U.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ),
  (etaleRestriction f).op.HasLeftKanExtension F]

section EdgeMap

variable (S : Scheme.{u})
variable [HasSheafify S.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [∀ U : S.Etale,
  HasWeakSheafify (S.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [HasDerivedCategory (Sheaf S.smallEtaleTopology (ModuleCat.{u} Λ))]

/-- The canonical cohomology edge map preserves addition. -/
theorem etaleDerivedHomShriekConstantToCohomology_map_add
    (M : DerivedCategory (Sheaf S.smallEtaleTopology (ModuleCat.{u} Λ)))
    (n : ℤ) (U : S.Etale) :
    let edge := fun φ : (DerivedCategory.singleFunctor
          (Sheaf S.smallEtaleTopology (ModuleCat.{u} Λ)) 0).obj
        (etaleExtensionByZeroConstantOver Λ U) ⟶ M⟦n⟧ ↦
        etaleSheafEvalUnitModule Λ U
          ((DerivedCategory.homologyFunctor
              (Sheaf S.smallEtaleTopology (ModuleCat.{u} Λ)) n).obj M)
          (etaleExtensionByZeroAdjunctionHomModule Λ U.hom (h := U.prop)
            (etaleConstantModule Λ U.left)
            ((DerivedCategory.homologyFunctor
                (Sheaf S.smallEtaleTopology (ModuleCat.{u} Λ)) n).obj M)
            (((DerivedCategory.singleFunctorCompHomologyFunctorIso
                (Sheaf S.smallEtaleTopology (ModuleCat.{u} Λ)) 0).inv.app
              (etaleExtensionByZeroConstantOver Λ U)) ≫
            (DerivedCategory.homologyFunctor
              (Sheaf S.smallEtaleTopology (ModuleCat.{u} Λ)) 0).map φ ≫
            (((DerivedCategory.homologyFunctor
              (Sheaf S.smallEtaleTopology (ModuleCat.{u} Λ)) 0).isoShift n).hom.app M)))
    ∀ φ ψ, edge (φ + ψ) = edge φ + edge ψ :=
  sorry

/-- The canonical cohomology edge map preserves scalar multiplication. -/
theorem etaleDerivedHomShriekConstantToCohomology_map_smul
    (M : DerivedCategory (Sheaf S.smallEtaleTopology (ModuleCat.{u} Λ)))
    (n : ℤ) (U : S.Etale) :
    let edge := fun φ : (DerivedCategory.singleFunctor
          (Sheaf S.smallEtaleTopology (ModuleCat.{u} Λ)) 0).obj
        (etaleExtensionByZeroConstantOver Λ U) ⟶ M⟦n⟧ ↦
        etaleSheafEvalUnitModule Λ U
          ((DerivedCategory.homologyFunctor
              (Sheaf S.smallEtaleTopology (ModuleCat.{u} Λ)) n).obj M)
          (etaleExtensionByZeroAdjunctionHomModule Λ U.hom (h := U.prop)
            (etaleConstantModule Λ U.left)
            ((DerivedCategory.homologyFunctor
                (Sheaf S.smallEtaleTopology (ModuleCat.{u} Λ)) n).obj M)
            (((DerivedCategory.singleFunctorCompHomologyFunctorIso
                (Sheaf S.smallEtaleTopology (ModuleCat.{u} Λ)) 0).inv.app
              (etaleExtensionByZeroConstantOver Λ U)) ≫
            (DerivedCategory.homologyFunctor
              (Sheaf S.smallEtaleTopology (ModuleCat.{u} Λ)) 0).map φ ≫
            (((DerivedCategory.homologyFunctor
              (Sheaf S.smallEtaleTopology (ModuleCat.{u} Λ)) 0).isoShift n).hom.app M)))
    ∀ (a : Λ) φ, edge (a • φ) = a • edge φ :=
  sorry

/-- The canonical edge map from derived Hom out of an extended constant sheaf
to sections of the cohomology sheaf. -/
def etaleDerivedHomShriekConstantToCohomology (M : DerivedCategory (Sheaf S.smallEtaleTopology (ModuleCat.{u} Λ)))
    (n : ℤ) (U : S.Etale) :
    ((linearYoneda Λ (DerivedCategory (Sheaf S.smallEtaleTopology (ModuleCat.{u} Λ)))).obj (M⟦n⟧)).obj
        (op ((DerivedCategory.singleFunctor
            (Sheaf S.smallEtaleTopology (ModuleCat.{u} Λ)) 0).obj
          (etaleExtensionByZeroConstantOver Λ U))) ⟶
      ((DerivedCategory.homologyFunctor
          (Sheaf S.smallEtaleTopology (ModuleCat.{u} Λ)) n).obj M).obj.obj
        (op U) :=
  ModuleCat.ofHom
    { toFun := fun φ ↦
        etaleSheafEvalUnitModule Λ U
          ((DerivedCategory.homologyFunctor
              (Sheaf S.smallEtaleTopology (ModuleCat.{u} Λ)) n).obj M)
          (etaleExtensionByZeroAdjunctionHomModule Λ U.hom (h := U.prop)
            (etaleConstantModule Λ U.left)
            ((DerivedCategory.homologyFunctor
                (Sheaf S.smallEtaleTopology (ModuleCat.{u} Λ)) n).obj M)
            (((DerivedCategory.singleFunctorCompHomologyFunctorIso
                (Sheaf S.smallEtaleTopology (ModuleCat.{u} Λ)) 0).inv.app
              (etaleExtensionByZeroConstantOver Λ U)) ≫
            (DerivedCategory.homologyFunctor
              (Sheaf S.smallEtaleTopology (ModuleCat.{u} Λ)) 0).map φ ≫
            (((DerivedCategory.homologyFunctor
              (Sheaf S.smallEtaleTopology (ModuleCat.{u} Λ)) 0).isoShift n).hom.app M)))
      map_add' := etaleDerivedHomShriekConstantToCohomology_map_add Λ S M n U
      map_smul' := etaleDerivedHomShriekConstantToCohomology_map_smul Λ S M n U }

/-- The edge map applies degree-zero homology, the single-object comparison,
the homology shift, the sheaf adjunction, and unit-section evaluation. -/
theorem etaleDerivedHomShriekConstantToCohomology_spec
    (M : DerivedCategory (Sheaf S.smallEtaleTopology (ModuleCat.{u} Λ))) (n : ℤ) (U : S.Etale)
    (φ :
      (DerivedCategory.singleFunctor
          (Sheaf S.smallEtaleTopology (ModuleCat.{u} Λ)) 0).obj
        (etaleExtensionByZeroConstantOver Λ U) ⟶
      M⟦n⟧) :
    etaleDerivedHomShriekConstantToCohomology Λ S M n U φ =
      etaleSheafEvalUnitModule Λ U
        ((DerivedCategory.homologyFunctor
            (Sheaf S.smallEtaleTopology (ModuleCat.{u} Λ)) n).obj M)
        (etaleExtensionByZeroAdjunctionHomModule Λ U.hom (h := U.prop)
          (etaleConstantModule Λ U.left)
          ((DerivedCategory.homologyFunctor
              (Sheaf S.smallEtaleTopology (ModuleCat.{u} Λ)) n).obj M)
          (((DerivedCategory.singleFunctorCompHomologyFunctorIso
                (Sheaf S.smallEtaleTopology (ModuleCat.{u} Λ)) 0).inv.app
              (etaleExtensionByZeroConstantOver Λ U)) ≫
            (DerivedCategory.homologyFunctor
              (Sheaf S.smallEtaleTopology (ModuleCat.{u} Λ)) 0).map φ ≫
            (((DerivedCategory.homologyFunctor
              (Sheaf S.smallEtaleTopology (ModuleCat.{u} Λ)) 0).isoShift n).hom.app M))) :=
  rfl

end EdgeMap

variable {Y : Scheme.{u}} (X : Over Y)
variable [IsSeparated X.hom] [Scheme.Hom.FiniteType X.hom]
variable [CompactSpace Y] [QuasiSeparatedSpace Y]
variable [CompactSpace X.left] [QuasiSeparatedSpace X.left]
variable (P : Compactification.Of Y X)
variable [HasSheafify X.left.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [∀ U : X.left.Etale,
  HasWeakSheafify (X.left.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [HasDerivedCategory (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [HasSheafify P.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [∀ U : P.obj.right.left.Etale,
  HasWeakSheafify (P.obj.right.left.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [HasDerivedCategory
  (Sheaf P.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [HasSheafify Y.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [∀ U : Y.Etale,
  HasWeakSheafify (Y.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [HasDerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [∀ F : X.left.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (etaleRestriction (Compactification.Of.ι P)).op.HasLeftKanExtension F]
variable [(etaleExtensionByZero (Compactification.Of.ι P)
    (ModuleCat.{u} Λ)).Additive]
variable [PreservesFiniteLimits
  (etaleExtensionByZero (Compactification.Of.ι P) (ModuleCat.{u} Λ))]
variable [PreservesFiniteColimits
  (etaleExtensionByZero (Compactification.Of.ι P) (ModuleCat.{u} Λ))]
variable [((smallEtalePullback P.obj.right.hom).sheafPushforwardContinuous
    (ModuleCat.{u} Λ) Y.smallEtaleTopology
    P.obj.right.left.smallEtaleTopology).Additive]
variable [HasRightDerivedFunctor
  (RightDerived.Cochain.toDerived
    ((smallEtalePullback P.obj.right.hom).sheafPushforwardContinuous
      (ModuleCat.{u} Λ) Y.smallEtaleTopology
      P.obj.right.left.smallEtaleTopology))
  (HomologicalComplex.quasiIso
    (Sheaf P.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ))
    (ComplexShape.up ℤ))]
variable [(etaleDerivedLowerShriek X P :
    DerivedCategory (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ)) ⥤
      DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ))).IsLeftAdjoint]
variable [HasSheafify (AffineEtale.topology X.left) (ModuleCat.{u} Λ)]
variable [(etaleDerivedLowerShriek X P :
    DerivedCategory (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ)) ⥤
      DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ))).CommShift ℤ]

/-- Shift compatibility of derived upper shriek transported from lower shriek
along their adjunction. -/
instance etaleDerivedUpperShriek_commShift :
    (etaleDerivedUpperShriek X Λ P).CommShift ℤ :=
  (etaleDerivedLowerShriekAdjunction X Λ P).rightAdjointCommShift ℤ

/-- The covariant functor `U ↦ R(U ⟶ Y)_! Λ` on `X.left.AffineEtale`, realized
as `Rf_!(j_U ! Λ)` via shriek composition. -/
def etaleDerivedLowerShriekConstant :
    X.left.AffineEtale ⥤ (DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ))) where
  obj U :=
    (etaleDerivedLowerShriek X P).obj
      ((DerivedCategory.singleFunctor
          (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ)) 0).obj
        (etaleExtensionByZeroConstantOver Λ ((AffineEtale.Spec X.left).obj U)))
  map {U U'} f :=
    (etaleDerivedLowerShriek X P).map
      ((DerivedCategory.singleFunctor
          (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ)) 0).map
        (etaleTraceOver Λ ((AffineEtale.Spec X.left).map f)))
  map_id U := by
    change (etaleDerivedLowerShriek X P).map
      ((DerivedCategory.singleFunctor
        (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ)) 0).map
          (etaleTraceOver Λ ((AffineEtale.Spec X.left).map (𝟙 U)))) = _
    rw [CategoryTheory.Functor.map_id, etaleTraceOver_id,
      CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]
  map_comp f g := by
    simp only [CategoryTheory.Functor.map_comp, ← etaleTraceOver_comp]

/-- Evaluating the affine constant lower shriek on `U` yields
`Rf_!(j_U ! Λ)`. -/
theorem etaleDerivedLowerShriekConstant_obj (U : X.left.AffineEtale) :
    (etaleDerivedLowerShriekConstant Λ X P).obj U =
      (etaleDerivedLowerShriek X P).obj
        ((DerivedCategory.singleFunctor
            (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ)) 0).obj
          (etaleExtensionByZeroConstantOver Λ
            ((AffineEtale.Spec X.left).obj U))) :=
  rfl

/-- The Hom presheaf `U ↦ Hom_Y(R(U ⟶ Y)_! Λ, K⟦n⟧)` on the affine étale site. -/
def etaleDerivedUpperShriekHomPresheaf (K : DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ))) (n : ℤ) :
    X.left.AffineEtaleᵒᵖ ⥤ ModuleCat.{u} Λ :=
  (etaleDerivedLowerShriekConstant Λ X P).op ⋙
    (linearYoneda Λ (DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ)))).obj (K⟦n⟧)

/-- The value of the Hom presheaf at `U` is the `Λ`-module of maps
`R(U ⟶ Y)_! Λ ⟶ K⟦n⟧` in `D(Y_étale, Λ)`. -/
theorem etaleDerivedUpperShriekHomPresheaf_obj (K : DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ))) (n : ℤ)
    (U : X.left.AffineEtaleᵒᵖ) :
    (etaleDerivedUpperShriekHomPresheaf Λ X P K n).obj U =
      ((linearYoneda Λ (DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ)))).obj (K⟦n⟧)).obj
        (op ((etaleDerivedLowerShriekConstant Λ X P).obj U.unop)) :=
  rfl

/-- The derived lower-shriek adjunction map preserves addition. -/
theorem etaleDerivedLowerShriekAdjunctionHomModule_map_add
    (L : DerivedCategory (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ))) (K : DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ)))
    (φ ψ : (etaleDerivedLowerShriek X P).obj L ⟶ K) :
    (etaleDerivedLowerShriekAdjunction X Λ P).homEquiv L K (φ + ψ) =
      (etaleDerivedLowerShriekAdjunction X Λ P).homEquiv L K φ +
      (etaleDerivedLowerShriekAdjunction X Λ P).homEquiv L K ψ :=
  sorry

/-- The derived lower-shriek adjunction map preserves scalar multiplication. -/
theorem etaleDerivedLowerShriekAdjunctionHomModule_map_smul
    (L : DerivedCategory (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ))) (K : DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ)))
    (a : Λ) (φ : (etaleDerivedLowerShriek X P).obj L ⟶ K) :
    (etaleDerivedLowerShriekAdjunction X Λ P).homEquiv L K (a • φ) =
      a • (etaleDerivedLowerShriekAdjunction X Λ P).homEquiv L K φ :=
  sorry

/-- The `Λ`-linear map on Hom-modules induced by the adjunction `Rf_! ⊣ Rf^!`. -/
def etaleDerivedLowerShriekAdjunctionHomModule
    (L : DerivedCategory (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ))) (K : DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ))) :
    ((linearYoneda Λ (DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ)))).obj K).obj
        (op ((etaleDerivedLowerShriek X P).obj L)) ⟶
      ((linearYoneda Λ (DerivedCategory (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ)))).obj
          ((etaleDerivedUpperShriek X Λ P).obj K)).obj (op L) :=
  ModuleCat.ofHom
    { toFun := (etaleDerivedLowerShriekAdjunction X Λ P).homEquiv L K
      map_add' := etaleDerivedLowerShriekAdjunctionHomModule_map_add Λ X P L K
      map_smul' := etaleDerivedLowerShriekAdjunctionHomModule_map_smul Λ X P L K }

/-- The Hom-module map of `Rf_! ⊣ Rf^!` is the adjunction hom-equivalence. -/
theorem etaleDerivedLowerShriekAdjunctionHomModule_spec
    (L : DerivedCategory (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ))) (K : DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ)))
    (φ : (etaleDerivedLowerShriek X P).obj L ⟶ K) :
    (etaleDerivedLowerShriekAdjunctionHomModule Λ X P L K) φ =
      (etaleDerivedLowerShriekAdjunction X Λ P).homEquiv L K φ :=
  rfl

/-- Component of the comparison at an affine étale object, sending a derived
Hom to the corresponding section of `H^n(Rf^! K)`. -/
def etaleDerivedUpperShriekHomToCohomology (K : DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ))) (n : ℤ)
    (U : X.left.AffineEtaleᵒᵖ) :
    (etaleDerivedUpperShriekHomPresheaf Λ X P K n).obj U ⟶
      (((AffineEtale.sheafEquiv X.left (ModuleCat.{u} Λ)).inverse.obj
          ((DerivedCategory.homologyFunctor
              (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ)) n).obj
            ((etaleDerivedUpperShriek X Λ P).obj K))).obj.obj U) :=
  let jU := (AffineEtale.Spec X.left).obj U.unop
  let L :=
    (DerivedCategory.singleFunctor
        (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ)) 0).obj
      (etaleExtensionByZeroConstantOver Λ jU)
  etaleDerivedLowerShriekAdjunctionHomModule Λ X P L (K⟦n⟧) ≫
    ModuleCat.ofHom
      (rightComp Λ L
        (((etaleDerivedUpperShriek X Λ P).commShiftIso n).hom.app K)) ≫
      etaleDerivedHomShriekConstantToCohomology Λ X.left
        ((etaleDerivedUpperShriek X Λ P).obj K) n jU

/-- The affine comparison component is adjunction, then the shift isomorphism
of `Rf^!`, then the canonical cohomology edge map. -/
theorem etaleDerivedUpperShriekHomToCohomology_spec (K : DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ)))
    (n : ℤ) (U : X.left.AffineEtaleᵒᵖ) :
    etaleDerivedUpperShriekHomToCohomology Λ X P K n U =
      (let jU := (AffineEtale.Spec X.left).obj U.unop
        let L :=
          (DerivedCategory.singleFunctor
              (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ)) 0).obj
            (etaleExtensionByZeroConstantOver Λ jU)
        etaleDerivedLowerShriekAdjunctionHomModule Λ X P L (K⟦n⟧) ≫
          ModuleCat.ofHom
            (rightComp Λ L
              (((etaleDerivedUpperShriek X Λ P).commShiftIso n).hom.app K)) ≫
            etaleDerivedHomShriekConstantToCohomology Λ X.left
              ((etaleDerivedUpperShriek X Λ P).obj K) n jU) :=
  rfl

/-- The affine cohomology comparison components commute with restriction maps. -/
theorem etaleDerivedUpperShriekHomPresheafToRestriction_naturality
    (K : DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ))) (n : ℤ)
    {U V : X.left.AffineEtaleᵒᵖ} (f : U ⟶ V) :
    (etaleDerivedUpperShriekHomPresheaf Λ X P K n).map f ≫
        etaleDerivedUpperShriekHomToCohomology Λ X P K n V =
      etaleDerivedUpperShriekHomToCohomology Λ X P K n U ≫
        (((AffineEtale.sheafEquiv X.left (ModuleCat.{u} Λ)).inverse.obj
          ((DerivedCategory.homologyFunctor
            (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ)) n).obj
              ((etaleDerivedUpperShriek X Λ P).obj K))).obj.map f) :=
  sorry

/-- The presheaf map from `U ↦ Hom_Y(R(U ⟶ Y)_! Λ, K⟦n⟧)` to the restriction
of `H^n(Rf^! K)` to `X_affine,étale`. -/
def etaleDerivedUpperShriekHomPresheafToRestriction (K : DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ)))
    (n : ℤ) :
    etaleDerivedUpperShriekHomPresheaf Λ X P K n ⟶
      (sheafToPresheaf (AffineEtale.topology X.left) (ModuleCat.{u} Λ)).obj
        ((AffineEtale.sheafEquiv X.left (ModuleCat.{u} Λ)).inverse.obj
          ((DerivedCategory.homologyFunctor
              (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ)) n).obj
            ((etaleDerivedUpperShriek X Λ P).obj K))) where
  app U := etaleDerivedUpperShriekHomToCohomology Λ X P K n U
  naturality _ _ f :=
    etaleDerivedUpperShriekHomPresheafToRestriction_naturality Λ X P K n f

/-- The comparison morphism from the sheaf associated to
`U ↦ Hom_Y(R(U ⟶ Y)_! Λ, K⟦n⟧)` to the restriction of `H^n(Rf^! K)` to the
affine étale site. -/
def etaleDerivedUpperShriekCohomologyAffineComparison (K : DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ)))
    (n : ℤ) :
    (presheafToSheaf (AffineEtale.topology X.left) (ModuleCat.{u} Λ)).obj
        (etaleDerivedUpperShriekHomPresheaf Λ X P K n) ⟶
      (AffineEtale.sheafEquiv X.left (ModuleCat.{u} Λ)).inverse.obj
        ((DerivedCategory.homologyFunctor
            (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ)) n).obj
          ((etaleDerivedUpperShriek X Λ P).obj K)) :=
  ((sheafificationAdjunction (AffineEtale.topology X.left)
        (ModuleCat.{u} Λ)).homEquiv
      (etaleDerivedUpperShriekHomPresheaf Λ X P K n)
      ((AffineEtale.sheafEquiv X.left (ModuleCat.{u} Λ)).inverse.obj
        ((DerivedCategory.homologyFunctor
            (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ)) n).obj
          ((etaleDerivedUpperShriek X Λ P).obj K)))).symm
    (etaleDerivedUpperShriekHomPresheafToRestriction Λ X P K n)

/-- The comparison is the sheafification of the Hom-presheaf map into the
affine restriction of `H^n(Rf^! K)`. -/
theorem etaleDerivedUpperShriekCohomologyAffineComparison_spec
    (K : DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ))) (n : ℤ) :
    etaleDerivedUpperShriekCohomologyAffineComparison Λ X P K n =
      ((sheafificationAdjunction (AffineEtale.topology X.left)
            (ModuleCat.{u} Λ)).homEquiv
          (etaleDerivedUpperShriekHomPresheaf Λ X P K n)
          ((AffineEtale.sheafEquiv X.left (ModuleCat.{u} Λ)).inverse.obj
            ((DerivedCategory.homologyFunctor
                (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ)) n).obj
              ((etaleDerivedUpperShriek X Λ P).obj K)))).symm
        (etaleDerivedUpperShriekHomPresheafToRestriction Λ X P K n) :=
  rfl

/-- For a separated finite-type morphism between quasi-compact quasi-separated
schemes and torsion coefficients, the affine restriction of the cohomology sheaf
of derived upper shriek is the sheafification of the trace-induced Hom presheaf. -/
instance etaleDerivedUpperShriek_cohomology_affineEtale
    (hΛ : AddMonoid.IsTorsion Λ) (K : DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ))) (n : ℤ) :
    let _ := hΛ
    IsIso (etaleDerivedUpperShriekCohomologyAffineComparison Λ X P K n) :=
  sorry

end AlgebraicGeometry.Scheme.Etale

end
