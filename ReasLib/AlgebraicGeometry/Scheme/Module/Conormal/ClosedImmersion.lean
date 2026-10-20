/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.Topology.Sheaves.Sheafify
public import ReasLib.AlgebraicGeometry.Scheme.Module.Conormal.BaseChange
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Differentials.Conormal.ChangeOfPresentation
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.ClosedImmersion
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous.Restrict

/-!
# Conormal sheaves of closed immersions

This file relates the conormal sheaf of a closed immersion to the cotangent sheaf of its
kernel ideal.  It also records the canonical comparisons associated to a factorization through
an open immersion.
-/

@[expose] public section

open CategoryTheory TopCat TopologicalSpace
open SheafOfModules.RingedSite

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom.Conormal

variable {Z U X : Scheme.{u}}

/-- The ambient sheaf of kernel-cotangent modules `I / I²` associated to a scheme morphism. -/
noncomputable def idealCotangentSheaf (j : Z ⟶ U) : U.Modules :=
  SheafOfModules.RingedSite.conormalSourceOverSource
    (J := Opens.grothendieckTopology U) (O₂ := U.sheaf)
    (O₃ := (TopCat.Sheaf.pushforward CommRingCat.{u} j.base).obj Z.sheaf)
    (RingedSpace.Hom.commRingSheafPushforwardMap j.toShHom)

/-- On an open of the ambient scheme, a section of the kernel ideal maps to its cotangent
class and then to the sheafification of the sectionwise cotangent modules. -/
noncomputable def idealToCotangentApp (j : Z ⟶ U) (V : (Opens U)ᵒᵖ) :
    (RingedSpace.Hom.kernelIdealSheaf j.toShHom).val.obj V ⟶
      conormalObj (RingedSpace.Hom.commRingSheafPushforwardMap j.toShHom) V :=
  (SheafOfModules.RingedSite.KernelIdeal.sectionsIso
      (RingedSpace.Hom.commRingSheafPushforwardMap j.toShHom) V).hom ≫
    ConcreteCategory.ofHom
      (Ideal.toCotangent
        (conormalIdeal (RingedSpace.Hom.commRingSheafPushforwardMap j.toShHom) V))

/-- The sectionwise maps from the kernel ideal to its cotangent sheaf commute with restriction. -/
theorem idealToCotangent_naturality (j : Z ⟶ U) {V W : (Opens U)ᵒᵖ}
    (f : V ⟶ W) :
    (RingedSpace.Hom.kernelIdealSheaf j.toShHom).val.map f ≫
        (ModuleCat.restrictScalars ((U.ringCatSheaf.obj.map f).hom)).map
          (idealToCotangentApp j W) =
      idealToCotangentApp j V ≫
        (conormalPresheaf (J := Opens.grothendieckTopology U)
          (O₂ := U.sheaf)
          (O₃ := (TopCat.Sheaf.pushforward CommRingCat.{u} j.base).obj Z.sheaf)
          (RingedSpace.Hom.commRingSheafPushforwardMap j.toShHom)).map f := sorry

/-- The morphism of module presheaves sending kernel-ideal sections to their cotangent
classes. -/
noncomputable def idealToCotangentPresheaf (j : Z ⟶ U) :
    (RingedSpace.Hom.kernelIdealSheaf j.toShHom).val ⟶
      conormalPresheaf (J := Opens.grothendieckTopology U)
        (O₂ := U.sheaf)
        (O₃ := (TopCat.Sheaf.pushforward CommRingCat.{u} j.base).obj Z.sheaf)
        (RingedSpace.Hom.commRingSheafPushforwardMap j.toShHom) where
  app V := idealToCotangentApp j V
  naturality f := idealToCotangent_naturality j f

/-- The canonical morphism from the kernel ideal sheaf to its ambient cotangent sheaf. -/
noncomputable def idealToCotangent (j : Z ⟶ U) :
    RingedSpace.Hom.kernelIdealSheaf j.toShHom ⟶ idealCotangentSheaf j :=
  (asIso ((PresheafOfModules.sheafificationAdjunction
      (𝟙 U.ringCatSheaf.obj)).counit.app
        (RingedSpace.Hom.kernelIdealSheaf j.toShHom))).inv ≫
    (PresheafOfModules.sheafification (𝟙 U.ringCatSheaf.obj)).map
      (idealToCotangentPresheaf j)

/-- The kernel-ideal-to-cotangent morphism sends a section to its class modulo the square of
the ideal. -/
theorem idealToCotangent_toCotangent (j : Z ⟶ U) (V : (Opens U)ᵒᵖ)
    (x : (RingedSpace.Hom.kernelIdealSheaf j.toShHom).val.obj V) :
    idealToCotangentApp j V x =
      Ideal.toCotangent
        (conormalIdeal (RingedSpace.Hom.commRingSheafPushforwardMap j.toShHom) V)
        ((SheafOfModules.RingedSite.KernelIdeal.sectionsIso
          (RingedSpace.Hom.commRingSheafPushforwardMap j.toShHom) V).hom x) := sorry

/-- The adjoint-side square comparing the ambient structure map with its inverse-image
transpose. -/
theorem structureMapSquare (j : Z ⟶ U) :
    CommSq
      ((TopCat.Sheaf.pullbackPushforwardAdjunction
        CommRingCat.{u} j.toShHom.hom.base).unit.app U.sheaf)
      (RingedSpace.Hom.commRingSheafPushforwardMap j.toShHom)
      ((TopCat.Sheaf.pushforward CommRingCat.{u} j.toShHom.hom.base).map
        (RingedSpace.Hom.inverseImageStructureSheafHomComm j.toShHom))
      (𝟙 ((TopCat.Sheaf.pushforward CommRingCat.{u} j.toShHom.hom.base).obj Z.sheaf)) := by
  refine ⟨?_⟩
  simpa only [Category.comp_id, Functor.id_obj, Adjunction.homEquiv_unit,
    RingedSpace.Hom.inverseImageStructureSheafHomComm] using
    (Equiv.apply_symm_apply
      ((TopCat.Sheaf.pullbackPushforwardAdjunction
        CommRingCat.{u} j.toShHom.hom.base).homEquiv U.sheaf Z.sheaf)
      (RingedSpace.Hom.commRingSheafPushforwardMap j.toShHom))

/-- The canonical comparison from the ambient ideal-cotangent sheaf to the pushforward of the
conormal sheaf. -/
noncomputable def pushforwardConormalComparison (j : Z ⟶ U) :
    idealCotangentSheaf j ⟶
      (Scheme.Modules.pushforward j).obj (Scheme.Hom.conormalSheaf j) :=
  SheafOfModules.RingedSite.Conormal.InverseImage.comparisonOverMiddle
    (J := Opens.grothendieckTopology U) (K := Opens.grothendieckTopology Z)
    (Opens.map j.toShHom.hom.base)
    ((TopCat.Sheaf.pullbackPushforwardAdjunction
      CommRingCat.{u} j.toShHom.hom.base).unit.app U.sheaf)
    (𝟙 ((TopCat.Sheaf.pushforward CommRingCat.{u} j.toShHom.hom.base).obj Z.sheaf))
    (structureMapSquare j)

/-- The pullback comparison from the ambient ideal-cotangent sheaf to the conormal sheaf is the
mate of the pushforward comparison. -/
noncomputable def idealCotangentPullbackComparison (j : Z ⟶ U) :
    (Scheme.Modules.pullback j).obj (idealCotangentSheaf j) ⟶
      Scheme.Hom.conormalSheaf j :=
  ((Scheme.Modules.pullbackPushforwardAdjunction j).homEquiv _ _).symm
    (pushforwardConormalComparison j)

/-- Pulling the ambient ideal-cotangent sheaf back along a closed immersion gives its conormal
sheaf. -/
theorem idealCotangentPullbackComparison_isIso
    (j : Z ⟶ U) [IsClosedImmersion j] :
    IsIso (idealCotangentPullbackComparison j) := sorry

/-- The canonical comparison from the pullback of the kernel ideal to the conormal sheaf. -/
noncomputable def pullbackIdealComparison (j : Z ⟶ U) :
    (Scheme.Modules.pullback j).obj
        (RingedSpace.Hom.kernelIdealSheaf j.toShHom) ⟶
      Scheme.Hom.conormalSheaf j :=
  (Scheme.Modules.pullback j).map (idealToCotangent j) ≫
    idealCotangentPullbackComparison j

/-- For a closed immersion, the pullback of the kernel ideal is canonically its conormal
sheaf. -/
theorem pullbackIdealComparison_isIso
    (j : Z ⟶ U) [IsClosedImmersion j] :
    IsIso (pullbackIdealComparison j) := sorry

/-- For a closed immersion, its pushed-forward conormal sheaf is canonically the ambient
kernel-cotangent sheaf. -/
theorem pushforwardConormalComparison_isIso
    (j : Z ⟶ U) [IsClosedImmersion j] :
    IsIso (pushforwardConormalComparison j) := sorry

/-- The conormal comparison induced by a factorization `i = j ≫ k`, written as a map from the
conormal sheaf of `i` to that of `j`. -/
noncomputable def factorizationConormalComparison
    (i : Z ⟶ X) (j : Z ⟶ U) (k : U ⟶ X) (h : j ≫ k = i) :
    Scheme.Hom.conormalSheaf i ⟶ Scheme.Hom.conormalSheaf j :=
  (Scheme.Modules.pullbackId Z).inv.app (Scheme.Hom.conormalSheaf i) ≫
    map (f := 𝟙 Z) (i := j) (i' := i) (g := k) ⟨by simpa [h]⟩

/-- Factoring an immersion through an open immersion does not change its conormal sheaf. -/
theorem factorizationConormalComparison_isIso
    (i : Z ⟶ X) (j : Z ⟶ U) (k : U ⟶ X) (h : j ≫ k = i)
    [IsImmersion i] [IsClosedImmersion j] [IsOpenImmersion k] :
    IsIso (factorizationConormalComparison i j k h) := sorry

/-- The inverse-image structure-sheaf map of an open immersion is an isomorphism. -/
theorem openImmersionStructureMap_isIso
    (k : U ⟶ X) [H : IsOpenImmersion k] :
    IsIso (RingedSpace.Hom.inverseImageStructureSheafHomComm k.toShHom) := by
  let stalkIso (x : U) :
      IsIso ((TopCat.Presheaf.stalkFunctor CommRingCat x).map
        (RingedSpace.Hom.inverseImageStructureSheafHomComm k.toShHom).hom) := by
    let gamma0 :=
      (TopCat.Presheaf.stalkPullbackIso CommRingCat k.base X.presheaf x).hom
    let gamma1 :=
      (TopCat.Presheaf.stalkFunctor CommRingCat x).map
        (CategoryTheory.toSheafify (Opens.grothendieckTopology U)
          ((TopCat.Presheaf.pullback CommRingCat k.base).obj X.presheaf))
    let gamma2 :=
      (TopCat.Presheaf.stalkFunctor CommRingCat x).map
        ((TopCat.Sheaf.pullbackIso CommRingCat k.base).inv.app X.sheaf).hom
    let gamma :=
      gamma0 ≫ gamma1 ≫ gamma2
    have gamma0_isIso : IsIso gamma0 := by
      dsimp only [gamma0]
      infer_instance
    have gamma1_isIso : IsIso gamma1 := by
      dsimp only [gamma1]
      exact TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso x CommRingCat _
    have gamma2_isIso : IsIso gamma2 := by
      dsimp only [gamma2]
      infer_instance
    have gamma01_isIso : IsIso (gamma0 ≫ gamma1) :=
      IsIso.comp_isIso' (f := gamma0) (h := gamma1) gamma0_isIso gamma1_isIso
    have gamma_isIso : IsIso gamma := by
      change IsIso ((gamma0 ≫ gamma1) ≫ gamma2)
      exact IsIso.comp_isIso' (f := gamma0 ≫ gamma1) (h := gamma2)
        gamma01_isIso gamma2_isIso
    have gamma_comp :
        gamma ≫ (TopCat.Presheaf.stalkFunctor CommRingCat x).map
          (RingedSpace.Hom.inverseImageStructureSheafHomComm k.toShHom).hom =
            k.stalkMap x := by
      let alpha := RingedSpace.Hom.inverseImageStructureSheafHomComm k.toShHom
      let constructedAdj :=
        CategoryTheory.Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
          (Opens.map k.toShHom.hom.base) CommRingCat
          (Opens.grothendieckTopology X) (Opens.grothendieckTopology U)
      have hsheaf :
          constructedAdj.unit.app X.sheaf ≫
              (TopCat.Sheaf.pushforward CommRingCat k.base).map
                ((TopCat.Sheaf.pullbackIso CommRingCat k.base).inv.app X.sheaf ≫ alpha) =
            RingedSpace.Hom.commRingSheafPushforwardMap k.toShHom := by
        dsimp only [alpha, constructedAdj]
        rw [Functor.map_comp]
        erw [← Category.assoc]
        dsimp only [TopCat.Sheaf.pullbackIso,
          CategoryTheory.Adjunction.leftAdjointUniq_inv_app]
        erw [Adjunction.unit_leftAdjointUniq_hom_app]
        change ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat k.base).homEquiv
          X.sheaf U.sheaf)
            (RingedSpace.Hom.inverseImageStructureSheafHomComm k.toShHom) =
              RingedSpace.Hom.commRingSheafPushforwardMap k.toShHom
        exact Equiv.apply_symm_apply
          ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat k.base).homEquiv
            X.sheaf U.sheaf)
          (RingedSpace.Hom.commRingSheafPushforwardMap k.toShHom)
      have stalkPushforward_naturality
          {F G : TopCat.Presheaf CommRingCat U} (phi : F ⟶ G) :
          F.stalkPushforward CommRingCat k.base x ≫
              (TopCat.Presheaf.stalkFunctor CommRingCat x).map phi =
            (TopCat.Presheaf.stalkFunctor CommRingCat (k x)).map
                ((TopCat.Presheaf.pushforward CommRingCat k.base).map phi) ≫
              G.stalkPushforward CommRingCat k.base x := by
        apply TopCat.Presheaf.stalk_hom_ext
          ((TopCat.Presheaf.pushforward CommRingCat k.base).obj F)
        intro V hx
        rw [TopCat.Presheaf.stalkPushforward_germ_assoc]
        erw [TopCat.Presheaf.stalkFunctor_map_germ]
        erw [TopCat.Presheaf.stalkFunctor_map_germ_assoc]
        erw [TopCat.Presheaf.stalkPushforward_germ]
        change phi.app (Opposite.op ((Opens.map k.base).obj V)) ≫ _ =
          phi.app (Opposite.op ((Opens.map k.base).obj V)) ≫ _
        rfl
      have htail :
          gamma2 ≫ (TopCat.Presheaf.stalkFunctor CommRingCat x).map alpha.hom =
            (TopCat.Presheaf.stalkFunctor CommRingCat x).map
              (((TopCat.Sheaf.pullbackIso CommRingCat k.base).inv.app X.sheaf ≫
                alpha).hom) := by
        dsimp only [gamma2]
        exact ((TopCat.Presheaf.stalkFunctor CommRingCat x).map_comp _ _).symm
      have htail' :
          gamma1 ≫ (TopCat.Presheaf.stalkFunctor CommRingCat x).map
              (((TopCat.Sheaf.pullbackIso CommRingCat k.base).inv.app X.sheaf ≫
                alpha).hom) =
            (TopCat.Presheaf.stalkFunctor CommRingCat x).map
              (CategoryTheory.toSheafify (Opens.grothendieckTopology U)
                  ((TopCat.Presheaf.pullback CommRingCat k.base).obj X.presheaf) ≫
                ((TopCat.Sheaf.pullbackIso CommRingCat k.base).inv.app X.sheaf ≫
                  alpha).hom) := by
        dsimp only [gamma1]
        exact ((TopCat.Presheaf.stalkFunctor CommRingCat x).map_comp _ _).symm
      dsimp only [gamma]
      simp only [Category.assoc]
      change gamma0 ≫ gamma1 ≫ gamma2 ≫
          (TopCat.Presheaf.stalkFunctor CommRingCat x).map alpha.hom = k.stalkMap x
      erw [htail]
      erw [htail']
      dsimp only [gamma0, TopCat.Presheaf.stalkPullbackIso,
        TopCat.Presheaf.stalkPullbackHom]
      simp only [Category.assoc]
      erw [stalkPushforward_naturality]
      have hpresheaf := congrArg (fun phi ↦ phi.hom) hsheaf
      dsimp only [constructedAdj] at hpresheaf
      change
        (TopCat.Presheaf.pullbackPushforwardAdjunction CommRingCat k.base).unit.app
              X.presheaf ≫
            (TopCat.Presheaf.pushforward CommRingCat k.base).map
              (CategoryTheory.toSheafify (Opens.grothendieckTopology U)
                  ((TopCat.Presheaf.pullback CommRingCat k.base).obj X.presheaf) ≫
                ((TopCat.Sheaf.pullbackIso CommRingCat k.base).inv.app X.sheaf ≫
                  alpha).hom) = k.toShHom.hom.c at hpresheaf
      let beta0 :=
        (TopCat.Presheaf.pullbackPushforwardAdjunction CommRingCat k.base).unit.app
          X.presheaf
      let beta1 :=
        (TopCat.Presheaf.pushforward CommRingCat k.base).map
          (CategoryTheory.toSheafify (Opens.grothendieckTopology U)
              ((TopCat.Presheaf.pullback CommRingCat k.base).obj X.presheaf) ≫
            ((TopCat.Sheaf.pullbackIso CommRingCat k.base).inv.app X.sheaf ≫
              alpha).hom)
      let rho := U.presheaf.stalkPushforward CommRingCat k.base x
      change beta0 ≫ beta1 = k.toShHom.hom.c at hpresheaf
      change
        (TopCat.Presheaf.stalkFunctor CommRingCat (k x)).map beta0 ≫
            (TopCat.Presheaf.stalkFunctor CommRingCat (k x)).map beta1 ≫ rho =
          (TopCat.Presheaf.stalkFunctor CommRingCat (k x)).map k.toShHom.hom.c ≫ rho
      calc
        _ = ((TopCat.Presheaf.stalkFunctor CommRingCat (k x)).map beta0 ≫
              (TopCat.Presheaf.stalkFunctor CommRingCat (k x)).map beta1) ≫ rho :=
          (Category.assoc _ _ _).symm
        _ = (TopCat.Presheaf.stalkFunctor CommRingCat (k x)).map
              (beta0 ≫ beta1) ≫ rho := by
          rw [(TopCat.Presheaf.stalkFunctor CommRingCat (k x)).map_comp]
        _ = _ := by
          rw [hpresheaf]
          rfl
    have gamma_comp_isIso :
        IsIso (gamma ≫ (TopCat.Presheaf.stalkFunctor CommRingCat x).map
          (RingedSpace.Hom.inverseImageStructureSheafHomComm k.toShHom).hom) := by
      rw [gamma_comp]
      exact inferInstanceAs (IsIso (k.toLRSHom.stalkMap x))
    exact @IsIso.of_isIso_comp_left _ _ _ _ _ gamma
      ((TopCat.Presheaf.stalkFunctor CommRingCat x).map
        (RingedSpace.Hom.inverseImageStructureSheafHomComm k.toShHom).hom)
      gamma_isIso gamma_comp_isIso
  exact @TopCat.Presheaf.isIso_of_stalkFunctor_map_iso
    _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (RingedSpace.Hom.inverseImageStructureSheafHomComm k.toShHom) stalkIso

/-- The structure-sheaf presentation isomorphism induced by a factorization through an open
immersion. -/
noncomputable def factorizationPresentationIso
    (i : Z ⟶ X) (j : Z ⟶ U) (k : U ⟶ X) (h : j ≫ k = i)
    [IsOpenImmersion k] :
    (TopCat.Sheaf.pullback CommRingCat.{u} i.toShHom.hom.base).obj X.sheaf ≅
      (TopCat.Sheaf.pullback CommRingCat.{u} j.toShHom.hom.base).obj U.sheaf :=
  (TopCat.Sheaf.pullbackCongr (A := CommRingCat.{u})
      (congrArg (fun f : Z ⟶ X ↦ f.toShHom.hom.base) h)).symm.app X.sheaf ≪≫
    (TopCat.Sheaf.pullbackComp (A := CommRingCat.{u})
      j.toShHom.hom.base k.toShHom.hom.base).symm.app X.sheaf ≪≫
    (TopCat.Sheaf.pullback CommRingCat.{u} j.toShHom.hom.base).mapIso
      (@asIso _ _ _ _
        (RingedSpace.Hom.inverseImageStructureSheafHomComm k.toShHom)
        (openImmersionStructureMap_isIso k))

/-- The factorization presentation isomorphism intertwines the two inverse-image structure-sheaf
maps. -/
theorem factorizationPresentationIso_hom_comp
    (i : Z ⟶ X) (j : Z ⟶ U) (k : U ⟶ X) (h : j ≫ k = i)
    [IsOpenImmersion k] :
    (factorizationPresentationIso i j k h).hom ≫
        RingedSpace.Hom.inverseImageStructureSheafHomComm j.toShHom =
      RingedSpace.Hom.inverseImageStructureSheafHomComm i.toShHom := sorry

/-- The explicit comparison in the reverse direction for a closed immersion factored through
an open immersion. -/
noncomputable def factorizationConormalComparisonInv
    (i : Z ⟶ X) (j : Z ⟶ U) (k : U ⟶ X) (h : j ≫ k = i)
    [IsImmersion i] [IsClosedImmersion j] [IsOpenImmersion k] :
    Scheme.Hom.conormalSheaf j ⟶ Scheme.Hom.conormalSheaf i :=
  SheafOfModules.RingedSite.Conormal.ChangeOfPresentation.comparisonInv
    (RingedSpace.Hom.inverseImageStructureSheafHomComm i.toShHom)
    (RingedSpace.Hom.inverseImageStructureSheafHomComm j.toShHom)
    (factorizationPresentationIso i j k h)
    (factorizationPresentationIso_hom_comp i j k h)

/-- The factorization comparison followed by its explicit reverse is the identity. -/
theorem factorizationConormalComparison_hom_inv_id
    (i : Z ⟶ X) (j : Z ⟶ U) (k : U ⟶ X) (h : j ≫ k = i)
    [IsImmersion i] [IsClosedImmersion j] [IsOpenImmersion k] :
    factorizationConormalComparison i j k h ≫
      factorizationConormalComparisonInv i j k h = 𝟙 _ := sorry

/-- The explicit reverse followed by the factorization comparison is the identity. -/
theorem factorizationConormalComparison_inv_hom_id
    (i : Z ⟶ X) (j : Z ⟶ U) (k : U ⟶ X) (h : j ≫ k = i)
    [IsImmersion i] [IsClosedImmersion j] [IsOpenImmersion k] :
    factorizationConormalComparisonInv i j k h ≫
      factorizationConormalComparison i j k h = 𝟙 _ := sorry

/-- Factoring a closed immersion through an open immersion gives an explicit isomorphism of
conormal sheaves. -/
noncomputable def factorizationConormalComparisonIso
    (i : Z ⟶ X) (j : Z ⟶ U) (k : U ⟶ X) (h : j ≫ k = i)
    [IsImmersion i] [IsClosedImmersion j] [IsOpenImmersion k] :
    Scheme.Hom.conormalSheaf i ≅ Scheme.Hom.conormalSheaf j where
  hom := factorizationConormalComparison i j k h
  inv := factorizationConormalComparisonInv i j k h
  hom_inv_id := factorizationConormalComparison_hom_inv_id i j k h
  inv_hom_id := factorizationConormalComparison_inv_hom_id i j k h

/-- In a closed-then-open factorization, the conormal sheaf and the pullback of the kernel ideal
are canonically joined to the closed-immersion conormal sheaf by invertible comparison maps. -/
theorem factorizationPullbackComparisons
    (i : Z ⟶ X) (j : Z ⟶ U) (k : U ⟶ X) (h : j ≫ k = i)
    [IsImmersion i] [IsClosedImmersion j] [IsOpenImmersion k] :
    IsIso (factorizationConormalComparison i j k h) ∧
      IsIso (pullbackIdealComparison j) :=
  ⟨factorizationConormalComparison_isIso i j k h,
    pullbackIdealComparison_isIso j⟩

/-- In a closed-then-open factorization, the pushed-forward conormal sheaf and the ambient
kernel-cotangent sheaf are canonically joined to the pushed-forward closed-immersion conormal
sheaf by invertible comparison maps. -/
theorem factorizationPushforwardComparisons
    (i : Z ⟶ X) (j : Z ⟶ U) (k : U ⟶ X) (h : j ≫ k = i)
    [IsImmersion i] [IsClosedImmersion j] [IsOpenImmersion k] :
    IsIso ((Scheme.Modules.pushforward j).map
      (factorizationConormalComparison i j k h)) ∧
      IsIso (pushforwardConormalComparison j) :=
  ⟨((Scheme.Modules.pushforward j).mapIso
      (factorizationConormalComparisonIso i j k h)).isIso_hom,
    pushforwardConormalComparison_isIso j⟩

end AlgebraicGeometry.Scheme.Hom.Conormal
