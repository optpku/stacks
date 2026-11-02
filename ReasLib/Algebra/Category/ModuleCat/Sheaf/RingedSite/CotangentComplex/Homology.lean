/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.CotangentComplex
public import ReasLib.RingTheory.CotangentComplex.Functoriality
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
/-!
# Objectwise homology of the ring-level cotangent complex

This module owns the `B`-module presheaf `U ↦ H^i(L(B(U)/A(U)))` attached to a homomorphism
of sheaves of commutative rings, together with its associated sheaf of `B`-modules.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open AlgebraicTopology
open HomologicalComplex
open Opposite
open PresheafOfModules.DifferentialsConstruction
open SheafOfModules.RingedSite
open scoped Simplicial
open scoped IteratedEndofunctor

noncomputable section

universe u

namespace SheafOfModules.RingedSite.CotangentComplex.Homology

set_option backward.isDefEq.respectTransparency false in
private theorem resolution_augmentation_zero {D E : Type*} [Category D] [Category E]
    {L : D ⥤ E} {R : E ⥤ D} (adj : L ⊣ R) (Y : E) :
    (((Adjunction.SimplicialResolution.eval adj).obj Y).hom.app (op ⦋0⦌)) =
      adj.counit.app Y := by
  change ((Comonad.simplicialResolution.augmentation adj.toComonad).app (op ⦋0⦌)).app Y = _
  rw [Comonad.simplicialResolution.augmentation.app_zero]
  rfl

set_option backward.isDefEq.respectTransparency false in
private theorem resolution_augmentation_succ {D E : Type*} [Category D] [Category E]
    {L : D ⥤ E} {R : E ⥤ D} (adj : L ⊣ R) (Y : E) (n : ℕ) :
    (((Adjunction.SimplicialResolution.eval adj).obj Y).hom.app (op ⦋n + 1⦌)) =
      adj.counit.app (((Adjunction.SimplicialResolution.eval adj).obj Y).left.obj (op ⦋n⦌)) ≫
        (((Adjunction.SimplicialResolution.eval adj).obj Y).hom.app (op ⦋n⦌)) := by
  let V := (Adjunction.SimplicialResolution.eval adj).obj Y
  have h := V.hom.naturality (SimplexCategory.δ (Fin.last (n + 1))).op
  have hd : V.left.map (SimplexCategory.δ (Fin.last (n + 1))).op =
      adj.counit.app (V.left.obj (op ⦋n⦌)) := by
    change (adj.toComonad.simplicialResolution.δ (Fin.last (n + 1))).app Y = _
    rw [Comonad.simplicialResolution.face]
    cases n <;> simp only [IteratedEndofunctor.face, Fin.lastCases_last]
    all_goals exact Category.comp_id _
  change V.left.map (SimplexCategory.δ (Fin.last (n + 1))).op ≫
    V.hom.app (op ⦋n⦌) = V.hom.app (op ⦋n + 1⦌) ≫ 𝟙 _ at h
  rw [hd, Category.comp_id] at h
  exact h.symm

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
variable [J.HasSheafCompose (CategoryTheory.forget CommRingCat.{u})]
variable [HasWeakSheafify J CommRingCat.{u}]
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [HasColimitsOfShape (Discrete WalkingPair) CommRingCat.{u}]
variable {A B : Sheaf J CommRingCat.{u}}

/-- The degree-`i` homology of the ring-level cotangent complex of `φ` on an object of the
site. -/
def obj (φ : A ⟶ B) (i : ℤ) (X : Cᵒᵖ) : ModuleCat (B.obj.obj X) :=
  (RingHom.cotangentComplex (φ.hom.app X).hom).homology i

/-- The cochain map `L(B(X)/A(X)) ⟶ restrictScalars(L(B(Y)/A(Y)))` induced by restriction
along `f : X ⟶ Y`. -/
def complexMap (φ : A ⟶ B) {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    RingHom.cotangentComplex (φ.hom.app X).hom ⟶
      ((ModuleCat.restrictScalars (B.obj.map f).hom).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj
        (RingHom.cotangentComplex (φ.hom.app Y).hom) where
  f n :=
    (ModuleCat.extendRestrictScalarsAdj (B.obj.map f).hom).homEquiv _ _
      ((Algebra.CotangentComplex.map (φ.hom.app X).hom (φ.hom.app Y).hom
          (A.obj.map f).hom (B.obj.map f).hom
          (congrArg CommRingCat.Hom.hom (φ.hom.naturality f))).f n)
  comm' i j _ := by
    exact ((ModuleCat.extendRestrictScalarsAdj (B.obj.map f).hom).homEquiv_naturality_left_square
      _ _ _ _ ((Algebra.CotangentComplex.map (φ.hom.app X).hom (φ.hom.app Y).hom
        (A.obj.map f).hom (B.obj.map f).hom
        (congrArg CommRingCat.Hom.hom (φ.hom.naturality f))).comm i j).symm).symm

/-- Identifying the short complex of a restricted cotangent complex with the restricted
short complex of the original cotangent complex. -/
private def scRestrictIso (φ : A ⟶ B) (i : ℤ) {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    ((((ModuleCat.restrictScalars (B.obj.map f).hom).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj
        (RingHom.cotangentComplex (φ.hom.app Y).hom)).sc i) ≅
      ((RingHom.cotangentComplex (φ.hom.app Y).hom).sc i).map
        (ModuleCat.restrictScalars (B.obj.map f).hom) :=
  ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)

/-- Homology of the restricted ring-level cotangent complex, as restriction of scalars of
objectwise homology. -/
@[no_expose] def restrictHomologyIso (φ : A ⟶ B) (i : ℤ) {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    ((((ModuleCat.restrictScalars (B.obj.map f).hom).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj
        (RingHom.cotangentComplex (φ.hom.app Y).hom)).homology i) ≅
      (ModuleCat.restrictScalars (B.obj.map f).hom).obj (obj φ i Y) :=
  ShortComplex.homologyMapIso (scRestrictIso φ i f) ≪≫
    ((RingHom.cotangentComplex (φ.hom.app Y).hom).sc i).mapHomologyIso
      (ModuleCat.restrictScalars (B.obj.map f).hom)

/-- Restriction of objectwise cotangent homology along a morphism of the site. -/
def map (φ : A ⟶ B) (i : ℤ) {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    obj φ i X ⟶
      (ModuleCat.restrictScalars ((ringSheaf J B).obj.map f).hom).obj (obj φ i Y) :=
  homologyMap (complexMap φ f) i ≫ (restrictHomologyIso φ i f).hom

/-- Restriction on objectwise cotangent homology respects identity morphisms. -/
theorem map_id (φ : A ⟶ B) (i : ℤ) (X : Cᵒᵖ) :
    map φ i (𝟙 X) =
      (ModuleCat.restrictScalarsId' ((ringSheaf J B).obj.map (𝟙 X)).hom
        (congrArg RingCat.Hom.hom ((ringSheaf J B).obj.map_id X))).inv.app
          (obj φ i X) :=
  sorry

/-- Restriction on objectwise cotangent homology respects composition. -/
theorem map_comp (φ : A ⟶ B) (i : ℤ) {X Y Z : Cᵒᵖ}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    map φ i (f ≫ g) =
      map φ i f ≫ (ModuleCat.restrictScalars ((ringSheaf J B).obj.map f).hom).map
        (map φ i g) ≫
      (ModuleCat.restrictScalarsComp' ((ringSheaf J B).obj.map f).hom
        ((ringSheaf J B).obj.map g).hom ((ringSheaf J B).obj.map (f ≫ g)).hom
        (congrArg RingCat.Hom.hom ((ringSheaf J B).obj.map_comp f g))).inv.app
          (obj φ i Z) :=
  sorry

/-- The presheaf of `B`-modules with value `U ↦ H^i(L(B(U)/A(U)))`. -/
def presheaf (φ : A ⟶ B) (i : ℤ) : PresheafOfModules (ringSheaf J B).obj where
  obj X := obj φ i X
  map f := map φ i f
  map_id X := map_id φ i X
  map_comp f g := map_comp φ i f g

/-- The value of the homology presheaf is the homology of the section-ring cotangent complex. -/
theorem presheaf_obj (φ : A ⟶ B) (i : ℤ) (X : Cᵒᵖ) :
    (presheaf φ i).obj X = obj φ i X :=
  rfl

/-- The sheaf of `B`-modules associated to `U ↦ H^i(L(B(U)/A(U)))`. -/
def sheafify (φ : A ⟶ B) (i : ℤ) : SheafOfModules (ringSheaf J B) :=
  (PresheafOfModules.sheafification (𝟙 (ringSheaf J B).obj)).obj (presheaf φ i)

/-- The canonical `A(X)`-algebra map from the degree-zero ring-level standard term
to the sections of the sheaf-level polynomial presentation. -/
def standardTermUnderMapZero (φ : A ⟶ B) (X : Cᵒᵖ) :
    CommRingCat.Under.CotangentComplex.standardTerm
        (A.obj.obj X) (Under.mk (φ.hom.app X)) (op ⦋0⦌) ⟶
      Under.mk ((standardTerm A (Under.mk φ) (op ⦋0⦌)).hom.hom.app X) :=
  ((CommRingCat.Under.FreeAlgebra.adjunction (A.obj.obj X)).homEquiv
      ((CategoryTheory.forget CommRingCat.{u}).obj (B.obj.obj X))
      (Under.mk ((standardTerm A (Under.mk φ) (op ⦋0⦌)).hom.hom.app X))).symm
    ((CategoryTheory.Sheaf.FreeAlgebra.Presentation.generator A
        (Under.mk φ)).hom.app X)

/-- The free `A(X)`-algebra on sections of an `A`-algebra sheaf maps to the sections of the
free `A`-algebra sheaf. -/
def freeSectionsMap (Y : Under A) (X : Cᵒᵖ) :
    (CommRingCat.Under.FreeAlgebra.adjunction (A.obj.obj X)).toComonad.toFunctor.obj
        (Under.mk (Y.hom.hom.app X)) ⟶
      Under.mk
        (((SheafOfModules.RingedSite.CotangentComplex.freeForgetAdjunction A).toComonad.toFunctor.obj
            Y).hom.hom.app X) :=
  ((CommRingCat.Under.FreeAlgebra.adjunction (A.obj.obj X)).homEquiv
      (((Under.forget A ⋙
            sheafCompose J (CategoryTheory.forget CommRingCat.{u})).obj Y).obj.obj X)
      (Under.mk
        (((SheafOfModules.RingedSite.CotangentComplex.freeForgetAdjunction A).toComonad.toFunctor.obj
            Y).hom.hom.app X))).symm
    (((SheafOfModules.RingedSite.CotangentComplex.freeForgetAdjunction A).unit.app
        ((Under.forget A ⋙
            sheafCompose J (CategoryTheory.forget CommRingCat.{u})).obj Y)).hom.app X)

/-- The canonical `A(X)`-algebra map from a ring-level standard-resolution term to the
sections of the corresponding sheaf-level standard-resolution term. -/
def standardTermUnderMap (φ : A ⟶ B) (X : Cᵒᵖ) :
    ∀ n : ℕ,
      CommRingCat.Under.CotangentComplex.standardTerm
          (A.obj.obj X) (Under.mk (φ.hom.app X)) (op ⦋n⦌) ⟶
        Under.mk ((standardTerm A (Under.mk φ) (op ⦋n⦌)).hom.hom.app X)
  | 0 => standardTermUnderMapZero φ X
  | n + 1 =>
      (CommRingCat.Under.FreeAlgebra.adjunction
            (A.obj.obj X)).toComonad.toFunctor.map
          (standardTermUnderMap φ X n) ≫
        freeSectionsMap (standardTerm A (Under.mk φ) (op ⦋n⦌)) X

set_option backward.isDefEq.respectTransparency false in
omit [J.HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
  [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasColimitsOfShape (Discrete WalkingPair) CommRingCat.{u}] in
private theorem freeSectionsMap_comp_counit (Y : Under A) (X : Cᵒᵖ) :
    freeSectionsMap Y X ≫
      (Under.post (sheafToPresheaf J CommRingCat.{u} ⋙
        (CategoryTheory.evaluation Cᵒᵖ CommRingCat.{u}).obj X)).map
          ((freeForgetAdjunction A).counit.app Y) =
      (CommRingCat.Under.FreeAlgebra.adjunction (A.obj.obj X)).counit.app
        (Under.mk (Y.hom.hom.app X)) := by
  apply ((CommRingCat.Under.FreeAlgebra.adjunction (A.obj.obj X)).homEquiv _ _).injective
  erw [Adjunction.homEquiv_naturality_right, freeSectionsMap, Equiv.apply_symm_apply,
    ← (CommRingCat.Under.FreeAlgebra.adjunction (A.obj.obj X)).homEquiv_symm_id
      (Under.mk (Y.hom.hom.app X)), Equiv.apply_symm_apply]
  exact congrArg (fun f => f.hom.app X)
    ((freeForgetAdjunction A).right_triangle_components Y)

set_option maxHeartbeats 800000 in
set_option backward.isDefEq.respectTransparency false in
/-- Ring-level and sheaf-level standard-resolution augmentations are compatible with
`standardTermUnderMap`. -/
theorem standardTermUnderMap_comp_augmentation (φ : A ⟶ B) (X : Cᵒᵖ) (n : ℕ) :
    (CommRingCat.Under.CotangentComplex.standardAugmentation
          (A.obj.obj X) (Under.mk (φ.hom.app X)) (op ⦋n⦌)).hom =
      ((standardAugmentation A (Under.mk φ) (op ⦋n⦌)).hom.app X).hom.comp
        (standardTermUnderMap φ X n).right.hom := by
  let E : Under A ⥤ Under (A.obj.obj X) :=
    Under.post (sheafToPresheaf J CommRingCat.{u} ⋙
      (CategoryTheory.evaluation Cᵒᵖ CommRingCat.{u}).obj X)
  let adj := CommRingCat.Under.FreeAlgebra.adjunction (A.obj.obj X)
  let adj' := freeForgetAdjunction A
  have h : ∀ n : ℕ,
      (((Adjunction.SimplicialResolution.eval adj).obj (Under.mk (φ.hom.app X))).hom.app (op ⦋n⦌)) =
        standardTermUnderMap φ X n ≫
          E.map (((Adjunction.SimplicialResolution.eval adj').obj (Under.mk φ)).hom.app (op ⦋n⦌)) := by
    intro n
    induction n with
    | zero =>
        rw [resolution_augmentation_zero, resolution_augmentation_zero]
        exact (freeSectionsMap_comp_counit (Under.mk φ) X).symm
    | succ n ih =>
        rw [resolution_augmentation_succ, resolution_augmentation_succ,
          standardTermUnderMap, E.map_comp]
        simp only [Category.assoc]
        have hc := freeSectionsMap_comp_counit
          (standardTerm A (Under.mk φ) (op ⦋n⦌)) X
        rw [← Category.assoc (freeSectionsMap _ X)]
        erw [hc]
        calc
          _ = (adj.counit.app _ ≫ standardTermUnderMap φ X n) ≫
              E.map (((Adjunction.SimplicialResolution.eval adj').obj
                (Under.mk φ)).hom.app (op ⦋n⦌)) := by
            exact (congrArg (fun k => adj.counit.app _ ≫ k) ih).trans
              (Category.assoc _ _ _).symm
          _ = (adj.toComonad.toFunctor.map (standardTermUnderMap φ X n) ≫
                adj.counit.app _) ≫
              E.map (((Adjunction.SimplicialResolution.eval adj').obj
                (Under.mk φ)).hom.app (op ⦋n⦌)) :=
            congrArg (fun k => k ≫ E.map
              (((Adjunction.SimplicialResolution.eval adj').obj
                (Under.mk φ)).hom.app (op ⦋n⦌)))
              (adj.counit.naturality (standardTermUnderMap φ X n)).symm
          _ = _ := Category.assoc _ _ _
  exact congrArg (fun f => f.right.hom) (h n)

/-- The objectwise unit from ring-level Kähler differentials of a sheaf homomorphism to
the sections of the sheaf of relative differentials. -/
def differentialsEvaluationUnit {O₁ O₂ : Sheaf J CommRingCat.{u}} (ψ : O₁ ⟶ O₂)
    (X : Cᵒᵖ) :
    CommRingCat.KaehlerDifferential (ψ.hom.app X) ⟶
      (relativeDifferentials ψ).val.obj X :=
  ((PresheafOfModules.sheafificationAdjunction
      (𝟙 (ringSheaf J O₂).obj)).unit.app
    (relativeDifferentials' ψ.hom)).app X

/-- The Kähler-differential comparison induced by `standardTermUnderMap`. -/
def simplicialDifferentialsSections (φ : A ⟶ B) (X : Cᵒᵖ) (n : ℕ) :
    CommRingCat.KaehlerDifferential
        (CommRingCat.Under.CotangentComplex.standardTerm
          (A.obj.obj X) (Under.mk (φ.hom.app X)) (op ⦋n⦌)).hom ⟶
      (ModuleCat.restrictScalars (standardTermUnderMap φ X n).right.hom).obj
        (CommRingCat.KaehlerDifferential
          ((standardTerm A (Under.mk φ) (op ⦋n⦌)).hom.hom.app X)) :=
  CommRingCat.KaehlerDifferential.map
    ((Category.id_comp ((standardTerm A (Under.mk φ) (op ⦋n⦌)).hom.hom.app X)).trans
      (standardTermUnderMap φ X n).w.symm)

/-- Objectwise comparison from Kähler differentials of the evaluated sheaf-level
standard term to the restricted evaluation of the sheaf-level simplicial tensor term. -/
def omegaToRestrictedSimplicial (φ : A ⟶ B) (X : Cᵒᵖ) (n : ℕ) :
    CommRingCat.KaehlerDifferential
        ((standardTerm A (Under.mk φ) (op ⦋n⦌)).hom.hom.app X) ⟶
      (ModuleCat.restrictScalars
          ((standardAugmentation A (Under.mk φ) (op ⦋n⦌)).hom.app X).hom).obj
        ((SheafOfModules.evaluation.{u} (ringSheaf J B) X).obj ((simplicialModule A (Under.mk φ)).obj (op ⦋n⦌))) :=
  differentialsEvaluationUnit (standardTerm A (Under.mk φ) (op ⦋n⦌)).hom X ≫
    (((ChangeOfRings.extendRestrictAdjunction
        (ringSheafMap (standardAugmentation A (Under.mk φ) (op ⦋n⦌)))).unit.app
        (relativeDifferentials (standardTerm A (Under.mk φ) (op ⦋n⦌)).hom)).val.app X)

/-- The map on simplicial tensor terms from ring-level cotangent homology generators to
the evaluated sheaf-level simplicial tensor term. -/
def simplicialSectionsMap (φ : A ⟶ B) (X : Cᵒᵖ) (n : ℕ) :
    (CommRingCat.Under.CotangentComplex.simplicialModule
        (A.obj.obj X) (Under.mk (φ.hom.app X))).obj (op ⦋n⦌) ⟶
      (SheafOfModules.evaluation.{u} (ringSheaf J B) X).obj ((simplicialModule A (Under.mk φ)).obj (op ⦋n⦌)) :=
  ((ModuleCat.extendRestrictScalarsAdj
        (CommRingCat.Under.CotangentComplex.standardAugmentation
          (A.obj.obj X) (Under.mk (φ.hom.app X)) (op ⦋n⦌)).hom).homEquiv _ _).symm
    (simplicialDifferentialsSections φ X n ≫
      (ModuleCat.restrictScalars (standardTermUnderMap φ X n).right.hom).map
        (omegaToRestrictedSimplicial φ X n) ≫
      (ModuleCat.restrictScalarsComp'
          (standardTermUnderMap φ X n).right.hom
          ((standardAugmentation A (Under.mk φ) (op ⦋n⦌)).hom.app X).hom
          (CommRingCat.Under.CotangentComplex.standardAugmentation
            (A.obj.obj X) (Under.mk (φ.hom.app X)) (op ⦋n⦌)).hom
          (standardTermUnderMap_comp_augmentation φ X n)).inv.app _)

/-- Degreewise comparison of ring-level and evaluated sheaf-level cotangent complexes. -/
def sectionsComplexMap_f (φ : A ⟶ B) (X : Cᵒᵖ) (i : ℤ) :
    (RingHom.cotangentComplex (φ.hom.app X).hom).X i ⟶
      (((SheafOfModules.evaluation.{u} (ringSheaf J B) X).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (SheafOfModules.RingedSite.CotangentComplex.obj A (Under.mk φ))).X i :=
  match h : ComplexShape.embeddingDownNat.r i with
  | some n =>
      (extendXIso
            ((alternatingFaceMapComplex
                (ModuleCat.{u} (B.obj.obj X))).obj
              (CommRingCat.Under.CotangentComplex.simplicialModule
                (A.obj.obj X) (Under.mk (φ.hom.app X))))
            ComplexShape.embeddingDownNat
            (ComplexShape.embeddingDownNat.f_eq_of_r_eq_some h)).hom ≫
        simplicialSectionsMap φ X n ≫
        (SheafOfModules.evaluation.{u} (ringSheaf J B) X).map
          (extendXIso
              ((alternatingFaceMapComplex
                  (SheafOfModules (ringSheaf J B))).obj
                (simplicialModule A (Under.mk φ)))
              ComplexShape.embeddingDownNat
              (ComplexShape.embeddingDownNat.f_eq_of_r_eq_some h)).inv
  | none => 0

/-- The cochain map `L(B(X)/A(X)) ⟶ L(φ)(X)` induced by comparing standard-resolution
terms after evaluating the sheaf-level cotangent complex. -/
def sectionsComplexMap (φ : A ⟶ B) (X : Cᵒᵖ) :
    RingHom.cotangentComplex (φ.hom.app X).hom ⟶
      ((SheafOfModules.evaluation.{u} (ringSheaf J B) X).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (SheafOfModules.RingedSite.CotangentComplex.obj A (Under.mk φ)) where
  f i := sectionsComplexMap_f φ X i
  comm' := sorry

/-- Identifying the short complex of the evaluated sheaf cotangent complex with the
evaluated short complex. -/
private def scEvaluationIso (φ : A ⟶ B) (i : ℤ) (X : Cᵒᵖ) :
    ((((SheafOfModules.evaluation.{u} (ringSheaf J B) X).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (SheafOfModules.RingedSite.CotangentComplex.obj A (Under.mk φ))).sc i) ≅
      (@ShortComplex.map _ _ _ _ _ _
        ((SheafOfModules.RingedSite.CotangentComplex.obj A (Under.mk φ)).sc i) (SheafOfModules.evaluation.{u} (ringSheaf J B) X)
        (by constructor; intro M N; rfl)) :=
  ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _) (by simp only [Iso.refl_hom]; exact (Category.id_comp _).trans (Category.comp_id _).symm)
    (by simp only [Iso.refl_hom]; exact (Category.id_comp _).trans (Category.comp_id _).symm)

/-- Evaluation of sheaves of modules identifies cycles of the evaluated short complex of
`L(φ)` with the evaluated cycles. -/
private def cyclesEvaluationIso (φ : A ⟶ B) (i : ℤ) (X : Cᵒᵖ) :
    ((@ShortComplex.map _ _ _ _ _ _
        ((SheafOfModules.RingedSite.CotangentComplex.obj A (Under.mk φ)).sc i) (SheafOfModules.evaluation.{u} (ringSheaf J B) X)
        (by constructor; intro M N; rfl))).cycles ≅
      (SheafOfModules.evaluation.{u} (ringSheaf J B) X).obj ((SheafOfModules.RingedSite.CotangentComplex.obj A (Under.mk φ)).sc i).cycles :=
  ShortComplex.cyclesIsoKernel _ ≪≫
    (PreservesKernel.iso (SheafOfModules.evaluation.{u} (ringSheaf J B) X) ((SheafOfModules.RingedSite.CotangentComplex.obj A (Under.mk φ)).sc i).g).symm ≪≫
    (SheafOfModules.evaluation.{u} (ringSheaf J B) X).mapIso (ShortComplex.cyclesIsoKernel ((SheafOfModules.RingedSite.CotangentComplex.obj A (Under.mk φ)).sc i)).symm

set_option backward.isDefEq.respectTransparency false in
/-- The evaluated homology projection annihilates the boundaries in the evaluated complex. -/
private theorem homologyEvaluationComparison_condition (φ : A ⟶ B) (i : ℤ) (X : Cᵒᵖ) :
    ((@ShortComplex.map _ _ _ _ _ _
        ((SheafOfModules.RingedSite.CotangentComplex.obj A (Under.mk φ)).sc i) (SheafOfModules.evaluation.{u} (ringSheaf J B) X)
        (by constructor; intro M N; rfl))).toCycles ≫
      ((cyclesEvaluationIso φ i X).hom ≫
        (SheafOfModules.evaluation.{u} (ringSheaf J B) X).map
          ((SheafOfModules.RingedSite.CotangentComplex.obj A (Under.mk φ)).sc i).homologyπ) = 0 :=
  by
    let S := (SheafOfModules.RingedSite.CotangentComplex.obj A (Under.mk φ)).sc i
    letI : (SheafOfModules.evaluation.{u} (ringSheaf J B) X).PreservesZeroMorphisms :=
      ⟨by intros; rfl⟩
    have hi : (cyclesEvaluationIso φ i X).hom ≫
        (SheafOfModules.evaluation.{u} (ringSheaf J B) X).map S.iCycles =
        (S.map (SheafOfModules.evaluation.{u} (ringSheaf J B) X)).iCycles := by
      simp [cyclesEvaluationIso, S, ← Functor.map_comp, Category.assoc]
      exact kernel.lift_ι _ _ _
    have hf : (S.map (SheafOfModules.evaluation.{u} (ringSheaf J B) X)).toCycles ≫
        (cyclesEvaluationIso φ i X).hom =
        (SheafOfModules.evaluation.{u} (ringSheaf J B) X).map S.toCycles := by
      apply (cancel_mono
        ((SheafOfModules.evaluation.{u} (ringSheaf J B) X).map S.iCycles)).1
      rw [Category.assoc, hi, ShortComplex.toCycles_i, ← Functor.map_comp,
        ShortComplex.toCycles_i]
      rfl
    change (S.map (SheafOfModules.evaluation.{u} (ringSheaf J B) X)).toCycles ≫
      ((cyclesEvaluationIso φ i X).hom ≫
        (SheafOfModules.evaluation.{u} (ringSheaf J B) X).map S.homologyπ) = 0
    rw [← Category.assoc, hf, ← Functor.map_comp, ShortComplex.toCycles_comp_homologyπ,
      Functor.map_zero]

/-- Homology of the evaluated sheaf-level cotangent complex maps to the evaluation of
sheaf homology. -/
@[no_expose] def homologyEvaluationComparison (φ : A ⟶ B) (i : ℤ) (X : Cᵒᵖ) :
    ((((SheafOfModules.evaluation.{u} (ringSheaf J B) X).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (SheafOfModules.RingedSite.CotangentComplex.obj A (Under.mk φ))).homology i) ⟶
      (SheafOfModules.evaluation.{u} (ringSheaf J B) X).obj ((SheafOfModules.RingedSite.CotangentComplex.obj A (Under.mk φ)).homology i) :=
  (ShortComplex.homologyMapIso (scEvaluationIso φ i X)).hom ≫
    ((@ShortComplex.map _ _ _ _ _ _
        ((SheafOfModules.RingedSite.CotangentComplex.obj A (Under.mk φ)).sc i) (SheafOfModules.evaluation.{u} (ringSheaf J B) X)
        (by constructor; intro M N; rfl))).descHomology
      ((cyclesEvaluationIso φ i X).hom ≫
        (SheafOfModules.evaluation.{u} (ringSheaf J B) X).map ((SheafOfModules.RingedSite.CotangentComplex.obj A (Under.mk φ)).sc i).homologyπ)
      (homologyEvaluationComparison_condition φ i X)

/-- Objectwise comparison from ring-level cotangent homology to sections of the homology
sheaf of `L(φ)`. -/
def presheafComparisonApp (φ : A ⟶ B) (i : ℤ) (X : Cᵒᵖ) :
    obj φ i X ⟶
      ((SheafOfModules.forget (ringSheaf J B)).obj
        ((SheafOfModules.RingedSite.CotangentComplex.obj A (Under.mk φ)).homology i)).obj X :=
  homologyMap (sectionsComplexMap φ X) i ≫ homologyEvaluationComparison φ i X

/-- The morphism of `B`-module presheaves sending `U ↦ H^i(L(B(U)/A(U)))` to the
underlying presheaf of `H^i(L(φ))`. -/
def presheafComparison (φ : A ⟶ B) (i : ℤ) :
    presheaf φ i ⟶
      (PresheafOfModules.restrictScalars (𝟙 (ringSheaf J B).obj)).obj
        ((SheafOfModules.forget (ringSheaf J B)).obj
          ((SheafOfModules.RingedSite.CotangentComplex.obj A (Under.mk φ)).homology i)) where
  app X := presheafComparisonApp φ i X
  naturality := sorry

/-- The canonical comparison from the associated sheaf of `U ↦ H^i(L(B(U)/A(U)))` to
the cohomology sheaf `H^i(L(φ))`. -/
def comparison (φ : A ⟶ B) (i : ℤ) :
    sheafify φ i ⟶ (SheafOfModules.RingedSite.CotangentComplex.obj A (Under.mk φ)).homology i :=
  (PresheafOfModules.sheafificationHomEquiv
      (𝟙 (ringSheaf J B).obj)).symm (presheafComparison φ i)

/-- The comparison morphism is the sheafification adjunct of `presheafComparison`. -/
theorem comparison_spec (φ : A ⟶ B) (i : ℤ) :
    PresheafOfModules.sheafificationHomEquiv (𝟙 (ringSheaf J B).obj)
        (comparison φ i) =
      presheafComparison φ i :=
  (PresheafOfModules.sheafificationHomEquiv (𝟙 (ringSheaf J B).obj)).apply_symm_apply
    (presheafComparison φ i)

/-- The canonical comparison from sheafified section-ring cotangent homology to
homology of the sheaf cotangent complex is an isomorphism in every integer degree. -/
instance comparison_isIso (φ : A ⟶ B) (i : ℤ) :
    IsIso (comparison φ i) := sorry

end SheafOfModules.RingedSite.CotangentComplex.Homology

