/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.GlobalSections
public import ReasLib.Topology.Opens.SectionComparison
public import ReasLib.Topology.Sheaf.CompactOpen.Intersection
public import ReasLib.Topology.Sheaf.OpenSubset

/-!
# Structure-sheaf sections on subsets

This module defines sections of the pullback of a scheme's structure sheaf to an arbitrary
subset, together with the algebra structure induced by a morphism to an affine scheme.
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

/-- The ring of sections of the restricted structure sheaf on a subset `E` of a scheme `X`. -/
abbrev subsetSectionsRing (X : Scheme.{u}) (E : Set X) : CommRingCat.{u} :=
  TopCat.Sheaf.CompactOpen.Intersection.target E X.sheaf

/-- `subsetSectionsRing X E` is the value at the top open of the pullback of `X.sheaf` to
the subspace carried by `E`. -/
theorem subsetSectionsRing_def (X : Scheme.{u}) (E : Set X) :
    X.subsetSectionsRing E =
      ((TopCat.Sheaf.pullback CommRingCat (TopCat.subsetInclusion E)).obj X.sheaf).presheaf.obj
        (op (⊤ : TopologicalSpace.Opens (TopCat.subsetSpace E))) := by
  rfl

/-- Restriction from global sections of `X` to sections of its structure sheaf on `E`. -/
noncomputable def subsetRestriction (X : Scheme.{u}) (E : Set X) :
    Γ(X, ⊤) ⟶ X.subsetSectionsRing E :=
  (((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat
    (TopCat.subsetInclusion E)).unit.app X.sheaf).1.app
      (op (⊤ : TopologicalSpace.Opens X)))

/-- The subset restriction is the adjunction-unit map on the top open followed by transport
along `Opens.map_top`. -/
theorem subsetRestriction_eq (X : Scheme.{u}) (E : Set X) :
    X.subsetRestriction E =
      (((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat
          (TopCat.subsetInclusion E)).unit.app X.sheaf).1.app
            (op (⊤ : TopologicalSpace.Opens X))) ≫
        eqToHom (congrArg
          (fun U : TopologicalSpace.Opens (TopCat.subsetSpace E) ↦
            ((TopCat.Sheaf.pullback CommRingCat
              (TopCat.subsetInclusion E)).obj X.sheaf).presheaf.obj (op U))
          (Opens.map_top (TopCat.subsetInclusion E))) := by
  rfl

/-- For an open subset `U`, sections on its underlying subset agree with global sections of the
restricted open subscheme. -/
noncomputable def subsetSectionsRingIsoGlobalSectionsRingRestrict
    (X : Scheme.{u}) (U : X.Opens) :
    X.subsetSectionsRing (U : Set X) ≅ Scheme.globalSectionsRing (X.restrict U.isOpenEmbedding) :=
      (((TopCat.Sheaf.forget CommRingCat (TopCat.Opens.Subspace.space U)).mapIso
        ((U.isOpenEmbedding.sheafPullbackIso CommRingCat).app X.sheaf)).app
          (op ((Opens.map (TopCat.Opens.Subspace.inclusion U)).obj ⊤))) ≪≫
      X.presheaf.mapIso (eqToIso (congrArg op (by
        rw [Opens.map_top, TopologicalSpace.Opens.isOpenEmbedding_obj_top]))) ≪≫
      U.topIso.symm

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Scheme.Hom

variable {A : Type u} [CommRing A]
variable {X : Scheme.{u}}

/-- The ring map from an affine base to sections of the restricted structure sheaf on `E`. -/
noncomputable def subsetSectionsMap
    (q : X ⟶ Spec (CommRingCat.of A)) (E : Set X) :
    A →+* X.subsetSectionsRing E :=
  (((Scheme.ΓSpecIso (CommRingCat.of A)).inv) ≫ q.appTop ≫ X.subsetRestriction E).hom

/-- The affine-base map on subset sections is the composite of `ΓSpecIso`, `q.appTop`, and
restriction to the subset. -/
theorem subsetSectionsMap_eq_appTop
    (q : X ⟶ Spec (CommRingCat.of A)) (E : Set X) :
    subsetSectionsMap q E =
      (((Scheme.ΓSpecIso (CommRingCat.of A)).inv) ≫ q.appTop ≫ X.subsetRestriction E).hom := by
  rfl

/-- The `A`-algebra structure on subset sections induced by a morphism to `Spec A`. -/
noncomputable abbrev subsetSectionsAlgebra
    (q : X ⟶ Spec (CommRingCat.of A)) (E : Set X) :
    Algebra A (X.subsetSectionsRing E) :=
  (subsetSectionsMap q E).toAlgebra

/-- Subset sections bundled as an `A`-algebra through the chosen morphism to `Spec A`. -/
noncomputable def subsetSectionsAlg
    (q : X ⟶ Spec (CommRingCat.of A)) (E : Set X) : CommAlgCat A :=
  @CommAlgCat.of A _ (X.subsetSectionsRing E) _ (subsetSectionsAlgebra q E)

/-- Forgetting the bundled affine-base algebra recovers the intrinsic subset-section ring. -/
theorem subsetSectionsAlg_carrier
    (q : X ⟶ Spec (CommRingCat.of A)) (E : Set X) :
    (forget₂ (CommAlgCat A) CommRingCat).obj (subsetSectionsAlg q E) =
      X.subsetSectionsRing E := by
  rfl

/-- Global sections of a restricted open subscheme agree with ambient sections on that open. -/
noncomputable def globalSectionsAlgRestrictIsoSectionsAlgOverSpec
    (q : X ⟶ Spec (CommRingCat.of A)) (U : X.Opens) :
    globalSectionsAlg (X.ofRestrict U.isOpenEmbedding ≫ q) ≅
      sectionsAlgOverSpec q U := by
  let eRingCat :
      Scheme.globalSectionsRing (X.restrict U.isOpenEmbedding) ≅ Γ(X, U) :=
    U.topIso
  let eRing :
      (globalSectionsAlg (X.ofRestrict U.isOpenEmbedding ≫ q) : Type u) ≃+*
        (sectionsAlgOverSpec q U : Type u) := by
    change Scheme.globalSectionsRing (X.restrict U.isOpenEmbedding) ≃+* Γ(X, U)
    exact eRingCat.commRingCatIsoToRingEquiv
  let e :
      (globalSectionsAlg (X.ofRestrict U.isOpenEmbedding ≫ q) : Type u) ≃ₐ[A]
        (sectionsAlgOverSpec q U : Type u) :=
    AlgEquiv.ofRingEquiv (f := eRing) <| by
      intro a
      have hRestrict :
          U.ι.appTop ≫ U.topIso.hom =
            X.presheaf.map (homOfLE (x := U) le_top).op := by
        rw [Scheme.Opens.ι_appTop, Scheme.Opens.topIso_hom]
        exact (X.presheaf.map_comp _ _).symm.trans
          (congrArg X.presheaf.map (Subsingleton.elim _ _))
      have hMap :
          ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫
              (X.ofRestrict U.isOpenEmbedding ≫ q).appTop) ≫ eRingCat.hom =
            (Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ q.appLE ⊤ U le_top := by
        rw [Scheme.Hom.comp_appTop]
        calc
          (((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ q.appTop) ≫ U.ι.appTop) ≫
                U.topIso.hom =
              ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ q.appTop) ≫
                (U.ι.appTop ≫ U.topIso.hom) := Category.assoc _ _ _
          _ = ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ q.appTop) ≫
                X.presheaf.map (homOfLE (x := U) le_top).op := by rw [hRestrict]
          _ = (Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ q.appLE ⊤ U le_top := rfl
      change eRing (globalSectionsMap (X.ofRestrict U.isOpenEmbedding ≫ q) a) =
        sectionsMap q U a
      change eRingCat.hom (globalSectionsMap
        (X.ofRestrict U.isOpenEmbedding ≫ q) a) = sectionsMap q U a
      simpa only [globalSectionsMap_eq_appTop, sectionsMap,
        ConcreteCategory.comp_apply] using
        ConcreteCategory.congr_hom hMap a
  exact CommAlgCat.isoMk e

set_option backward.isDefEq.respectTransparency false in
/-- For an open subset, subset sections agree with the ordinary section algebra on that open. -/
noncomputable def subsetSectionsAlgIsoSectionsAlgOverSpec
    (q : X ⟶ Spec (CommRingCat.of A)) (U : X.Opens) :
    subsetSectionsAlg q (U : Set X) ≅
      sectionsAlgOverSpec q U := by
  let hOpen :
      U.isOpenEmbedding.functor.obj
          ((Opens.map (TopCat.Opens.Subspace.inclusion U)).obj ⊤) = U := by
    rw [Opens.map_top, TopologicalSpace.Opens.isOpenEmbedding_obj_top]
  let eRingCat : X.subsetSectionsRing (U : Set X) ≅ Γ(X, U) :=
    (((TopCat.Sheaf.forget CommRingCat (TopCat.Opens.Subspace.space U)).mapIso
      ((U.isOpenEmbedding.sheafPullbackIso CommRingCat).app X.sheaf)).app
        (op ((Opens.map (TopCat.Opens.Subspace.inclusion U)).obj ⊤))) ≪≫
      X.presheaf.mapIso (eqToIso (congrArg op hOpen))
  let eRing :
      (subsetSectionsAlg q (U : Set X) : Type u) ≃+*
        (sectionsAlgOverSpec q U : Type u) := by
    change X.subsetSectionsRing (U : Set X) ≃+* Γ(X, U)
    exact eRingCat.commRingCatIsoToRingEquiv
  let e :
      (subsetSectionsAlg q (U : Set X) : Type u) ≃ₐ[A]
        (sectionsAlgOverSpec q U : Type u) :=
    AlgEquiv.ofRingEquiv (f := eRing) <| by
      intro a
      have h := TopCat.Sheaf.OpenSubset.Restriction.openEmbeddingCounitEq
        (A := CommRingCat) U X.sheaf
      have hApp := congrArg
        (fun η ↦ η.app (op (⊤ : TopologicalSpace.Opens X))) h
      have hForget :
          ((TopCat.Sheaf.forget CommRingCat
            (TopCat.Opens.Subspace.space U)).map
              ((U.isOpenEmbedding.sheafPullbackIso CommRingCat).hom.app X.sheaf)).app
                (op ((Opens.map (TopCat.Opens.Subspace.inclusion U)).obj ⊤)) =
            (((U.isOpenEmbedding.sheafPullbackIso CommRingCat).app
              X.sheaf).hom).hom.app
                ((Opens.map (TopCat.Opens.Subspace.inclusion U)).op.obj
                  (op (⊤ : TopologicalSpace.Opens X))) := rfl
      have hUnit :
          (((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat
              (TopCat.Opens.Subspace.inclusion U)).unit.app X.sheaf).hom.app
                (op (⊤ : TopologicalSpace.Opens X))) ≫
            (((TopCat.Sheaf.forget CommRingCat
              (TopCat.Opens.Subspace.space U)).mapIso
                ((U.isOpenEmbedding.sheafPullbackIso CommRingCat).app X.sheaf)).app
                  (op ((Opens.map (TopCat.Opens.Subspace.inclusion U)).obj ⊤))).hom =
            (Functor.whiskerRight
              (NatTrans.op U.isOpenEmbedding.isOpenMap.adjunction.counit)
              X.sheaf.obj).app (op (⊤ : TopologicalSpace.Opens X)) := by
        change _ ≫
            ((TopCat.Sheaf.forget CommRingCat
              (TopCat.Opens.Subspace.space U)).map
                ((U.isOpenEmbedding.sheafPullbackIso CommRingCat).hom.app X.sheaf)).app
                  (op ((Opens.map (TopCat.Opens.Subspace.inclusion U)).obj ⊤)) = _
        rw [hForget]
        simpa only [NatTrans.comp_app, Functor.whiskerLeft_app, Iso.app_hom] using hApp.symm
      have hCounit :
          (Functor.whiskerRight
              (NatTrans.op U.isOpenEmbedding.isOpenMap.adjunction.counit)
              X.sheaf.obj).app (op (⊤ : TopologicalSpace.Opens X)) ≫
            X.presheaf.map (eqToHom (congrArg op hOpen)) =
          X.presheaf.map (homOfLE (x := U) le_top).op := by
        change X.presheaf.map _ ≫ X.presheaf.map _ = X.presheaf.map _
        rw [← X.presheaf.map_comp]
        congr 1
      have hRestriction :
          X.subsetRestriction (U : Set X) =
            (((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat
              (TopCat.Opens.Subspace.inclusion U)).unit.app X.sheaf).hom.app
                (op (⊤ : TopologicalSpace.Opens X))) := rfl
      have hMap :
          CommRingCat.ofHom (subsetSectionsMap q (U : Set X)) ≫ eRingCat.hom =
            CommRingCat.ofHom (sectionsMap q U) := by
        change _ = (Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ q.appLE ⊤ U le_top
        calc
          _ = ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ q.appTop) ≫
                (Functor.whiskerRight
                  (NatTrans.op U.isOpenEmbedding.isOpenMap.adjunction.counit)
                  X.sheaf.obj).app (op (⊤ : TopologicalSpace.Opens X)) ≫
              X.presheaf.map (eqToHom (congrArg op hOpen)) := by
            simp only [eRingCat, subsetSectionsMap, hRestriction,
              Iso.trans_hom, Functor.mapIso_hom,
              CommRingCat.hom_comp, CommRingCat.ofHom_hom, CommRingCat.ofHom_comp,
              eqToIso.hom]
            simpa only [Category.assoc] using congrArg
              (fun k ↦ (((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ q.appTop) ≫ k) ≫
                X.presheaf.map (eqToHom (congrArg op hOpen))) hUnit
          _ = ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ q.appTop) ≫
                X.presheaf.map (homOfLE (x := U) le_top).op := by
            simpa only [Category.assoc] using congrArg
              (fun k ↦ ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ q.appTop) ≫ k)
              hCounit
          _ = _ := rfl
      change eRing (subsetSectionsMap q (U : Set X) a) = sectionsMap q U a
      change eRingCat.hom (subsetSectionsMap q (U : Set X) a) = sectionsMap q U a
      have hMap' := congrArg (fun k ↦ k.hom) hMap
      exact DFunLike.congr_fun hMap' a
  exact CommAlgCat.isoMk e

/-- For an open subset, the subset-section algebra agrees with the global-sections algebra of the
restricted open subscheme. -/
noncomputable def subsetSectionsAlgIsoGlobalSectionsAlgRestrict
    (q : X ⟶ Spec (CommRingCat.of A)) (U : X.Opens) :
    subsetSectionsAlg q (U : Set X) ≅
      globalSectionsAlg (X.ofRestrict U.isOpenEmbedding ≫ q) :=
  subsetSectionsAlgIsoSectionsAlgOverSpec (q := q) U ≪≫
    (globalSectionsAlgRestrictIsoSectionsAlgOverSpec (q := q) U).symm

/-- The structure map of the bundled subset-section algebra is `subsetSectionsMap`. -/
theorem subsetSectionsAlg_map
    (q : X ⟶ Spec (CommRingCat.of A)) (E : Set X) :
    algebraMap A (subsetSectionsAlg q E) = subsetSectionsMap q E := by
  rfl

end AlgebraicGeometry.Scheme.Hom
