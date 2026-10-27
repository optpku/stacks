/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Topos.Module.Derived.CompositionIso
public import ReasLib.AlgebraicGeometry.RingedSite.Simplicial.DerivedModuleSystem
public import ReasLib.CategoryTheory.Sites.Simplicial.FaceDescent

/-! # Derived-module systems from a coface cocycle -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite Functor
open RingedSite
open scoped Simplicial

noncomputable section

universe u v w

namespace RingedSite.Simplicial.DerivedModuleSystem

variable (X : SimplexCategory → RingedSite.{u, v, w})
variable [∀ n, (X n).siteTopology.HasSheafCompose (forget RingCat.{w})]
variable [UnivLE.{max u v, w}]
variable (fHom : ∀ {m n : SimplexCategory}, (m ⟶ n) → ToposHom (X n) (X m))
variable [∀ {m n : SimplexCategory} (φ : m ⟶ n),
    (SheafOfModules.restrictScalars.{w} (fHom φ).structureMap).IsRightAdjoint]
variable [∀ {m n : SimplexCategory} (φ : m ⟶ n),
    ToposHom.HasModulePullbackDerived (fHom φ)]
variable (functoriality : RingedSite.Simplicial.ModulePullbackFunctoriality X fHom)

/-- Reidentify `Lf_φ^*` along an equality of simplex operators. -/
def recodePullback {m n : SimplexCategory} {φ ψ : m ⟶ n} (h : φ = ψ) :
    (fHom φ).modulePullbackDerived ≅ (fHom ψ).modulePullbackDerived :=
  eqToIso (congrArg (fun t : m ⟶ n ↦ (fHom t).modulePullbackDerived) h)

/-- `recodePullback` is the identity when the operator equality is `rfl`. -/
theorem recodePullback_refl {m n : SimplexCategory} (φ : m ⟶ n) :
    recodePullback X fHom (rfl : φ = φ) = Iso.refl _ :=
  rfl

/-- The pullback of `α` along a 2-face `δ i`, as a morphism in `D(O_2)`. -/
def facePullback (i : Fin 3)
    {K0 : RingedSite.Hom.ModuleDerived.{w} (X ⦋0⦌)}
    (α : (fHom (SimplexCategory.δ (1 : Fin 2))).modulePullbackDerived.obj K0 ≅
      (fHom (SimplexCategory.δ (0 : Fin 2))).modulePullbackDerived.obj K0) :
    (fHom (SimplexCategory.δ (1 : Fin 2) ≫ SimplexCategory.δ i)).modulePullbackDerived.obj K0 ⟶
      (fHom (SimplexCategory.δ (0 : Fin 2) ≫ SimplexCategory.δ i)).modulePullbackDerived.obj K0 :=
  (ToposHom.DerivedPullbackComposition.compComparisonIso
      (fHom (SimplexCategory.δ i)) (fHom (SimplexCategory.δ (1 : Fin 2))) (fHom ((SimplexCategory.δ (1 : Fin 2)) ≫ (SimplexCategory.δ i)))
      (functoriality.pullbackCompIso (SimplexCategory.δ (1 : Fin 2)) (SimplexCategory.δ i))).inv.app K0 ≫
    (fHom (SimplexCategory.δ i)).modulePullbackDerived.map α.hom ≫
    (ToposHom.DerivedPullbackComposition.compComparisonIso
      (fHom (SimplexCategory.δ i)) (fHom (SimplexCategory.δ (0 : Fin 2))) (fHom ((SimplexCategory.δ (0 : Fin 2)) ≫ (SimplexCategory.δ i)))
      (functoriality.pullbackCompIso (SimplexCategory.δ (0 : Fin 2)) (SimplexCategory.δ i))).hom.app K0

/-- `facePullback i α` is `Lf_{δ i}^* α` after the composition identifications. -/
theorem facePullback_eq (i : Fin 3)
    {K0 : RingedSite.Hom.ModuleDerived.{w} (X ⦋0⦌)}
    (α : (fHom (SimplexCategory.δ (1 : Fin 2))).modulePullbackDerived.obj K0 ≅
      (fHom (SimplexCategory.δ (0 : Fin 2))).modulePullbackDerived.obj K0) :
    facePullback X fHom functoriality i α =
      (ToposHom.DerivedPullbackComposition.compComparisonIso
      (fHom (SimplexCategory.δ i)) (fHom (SimplexCategory.δ (1 : Fin 2))) (fHom ((SimplexCategory.δ (1 : Fin 2)) ≫ (SimplexCategory.δ i)))
      (functoriality.pullbackCompIso (SimplexCategory.δ (1 : Fin 2)) (SimplexCategory.δ i))).inv.app K0 ≫
        (fHom (SimplexCategory.δ i)).modulePullbackDerived.map α.hom ≫
        (ToposHom.DerivedPullbackComposition.compComparisonIso
      (fHom (SimplexCategory.δ i)) (fHom (SimplexCategory.δ (0 : Fin 2))) (fHom ((SimplexCategory.δ (0 : Fin 2)) ≫ (SimplexCategory.δ i)))
      (functoriality.pullbackCompIso (SimplexCategory.δ (0 : Fin 2)) (SimplexCategory.δ i))).hom.app K0 :=
  by
    unfold facePullback
    apply congrArg₂ (fun a b ↦ a ≫ b)
    · rfl
    · apply congrArg₂ (fun a b ↦ a ≫ b) <;> rfl

/-- `(f_{δ 1})^{-1} α` transported to a morphism out of `Lf_{δ 1 ≫ δ 2}^* K_0`. -/
def cocycleLeft {K0 : RingedSite.Hom.ModuleDerived.{w} (X ⦋0⦌)}
    (α : (fHom (SimplexCategory.δ (1 : Fin 2))).modulePullbackDerived.obj K0 ≅
      (fHom (SimplexCategory.δ (0 : Fin 2))).modulePullbackDerived.obj K0) :
    (fHom (SimplexCategory.δ (1 : Fin 2) ≫ SimplexCategory.δ (2 : Fin 3))).modulePullbackDerived.obj
      K0 ⟶
      (fHom (SimplexCategory.δ (0 : Fin 2) ≫ SimplexCategory.δ (1 : Fin 3))).modulePullbackDerived.obj
        K0 :=
  (recodePullback X fHom (SimplexCategory.δ_comp_δ_self (i := (1 : Fin 2))).symm).hom.app K0 ≫
    facePullback X fHom functoriality 1 α

/-- `(f_{δ 0})^{-1} α ∘ (f_{δ 2})^{-1} α` after the `δ_comp_δ` identifications on `C_2`. -/
def cocycleRight {K0 : RingedSite.Hom.ModuleDerived.{w} (X ⦋0⦌)}
    (α : (fHom (SimplexCategory.δ (1 : Fin 2))).modulePullbackDerived.obj K0 ≅
      (fHom (SimplexCategory.δ (0 : Fin 2))).modulePullbackDerived.obj K0) :
    (fHom (SimplexCategory.δ (1 : Fin 2) ≫ SimplexCategory.δ (2 : Fin 3))).modulePullbackDerived.obj
      K0 ⟶
      (fHom (SimplexCategory.δ (0 : Fin 2) ≫ SimplexCategory.δ (1 : Fin 3))).modulePullbackDerived.obj
        K0 :=
  facePullback X fHom functoriality 2 α ≫
    (recodePullback X fHom
        (SimplexCategory.δ_comp_δ (i := (0 : Fin 2)) (j := (1 : Fin 2))
          (Fin.zero_le _))).hom.app K0 ≫
    facePullback X fHom functoriality 0 α ≫
    (recodePullback X fHom
        (SimplexCategory.δ_comp_δ (i := (0 : Fin 2)) (j := (0 : Fin 2))
          le_rfl).symm).hom.app K0

/-- `cocycleLeft` is `(f_{δ 1})^{-1} α` after recoding along `δ_comp_δ_self`. -/
theorem cocycleLeft_eq {K0 : RingedSite.Hom.ModuleDerived.{w} (X ⦋0⦌)}
    (α : (fHom (SimplexCategory.δ (1 : Fin 2))).modulePullbackDerived.obj K0 ≅
      (fHom (SimplexCategory.δ (0 : Fin 2))).modulePullbackDerived.obj K0) :
    cocycleLeft X fHom functoriality α =
      (recodePullback X fHom (SimplexCategory.δ_comp_δ_self (i := (1 : Fin 2))).symm).hom.app K0 ≫
        facePullback X fHom functoriality 1 α :=
  by
    unfold cocycleLeft
    apply congrArg₂ (fun a b ↦ a ≫ b)
    · apply NatTrans.congr_app
      apply congrArg Iso.hom
      apply congrArg (recodePullback X fHom)
      exact Subsingleton.elim _ _
    · rfl

/-- `cocycleRight` is `(f_{δ 0})^{-1} α ∘ (f_{δ 2})^{-1} α` after the `δ_comp_δ`
identifications. -/
theorem cocycleRight_eq {K0 : RingedSite.Hom.ModuleDerived.{w} (X ⦋0⦌)}
    (α : (fHom (SimplexCategory.δ (1 : Fin 2))).modulePullbackDerived.obj K0 ≅
      (fHom (SimplexCategory.δ (0 : Fin 2))).modulePullbackDerived.obj K0) :
    cocycleRight X fHom functoriality α =
      facePullback X fHom functoriality 2 α ≫
        (recodePullback X fHom
            (SimplexCategory.δ_comp_δ (i := (0 : Fin 2)) (j := (1 : Fin 2))
              (Fin.zero_le _))).hom.app K0 ≫
        facePullback X fHom functoriality 0 α ≫
        (recodePullback X fHom
            (SimplexCategory.δ_comp_δ (i := (0 : Fin 2)) (j := (0 : Fin 2))
              le_rfl).symm).hom.app K0 :=
  by
    unfold cocycleRight
    apply congrArg₂ (fun a b ↦ a ≫ b)
    · rfl
    · apply congrArg₂ (fun a b ↦ a ≫ b)
      · apply NatTrans.congr_app
        apply congrArg Iso.hom
        apply congrArg (recodePullback X fHom)
        exact Subsingleton.elim _ _
      · apply congrArg₂ (fun a b ↦ a ≫ b)
        · rfl
        · apply NatTrans.congr_app
          apply congrArg Iso.hom
          apply congrArg (recodePullback X fHom)
          exact Subsingleton.elim _ _

/-- The stage object `K_n = Lf_{τ^n_n}^* K_0`. -/
def ofCocycleObj (K0 : RingedSite.Hom.ModuleDerived.{w} (X ⦋0⦌)) (n : SimplexCategory) :
    RingedSite.Hom.ModuleDerived.{w} (X n) :=
  (fHom (CategoryTheory.SimplicialSites.Sheaf.vertexOp n)).modulePullbackDerived.obj K0

/-- `ofCocycleObj K0 n` is the vertex pullback `Lf_{τ^n_n}^* K_0`. -/
theorem ofCocycleObj_eq (K0 : RingedSite.Hom.ModuleDerived.{w} (X ⦋0⦌)) (n : SimplexCategory) :
    ofCocycleObj X fHom K0 n = (fHom (CategoryTheory.SimplicialSites.Sheaf.vertexOp n)).modulePullbackDerived.obj K0 :=
  rfl

/-- The edge-pullback comparison isomorphism `K_φ : Lf_φ^* K_m ≅ K_n`, obtained by recoding along
`τ^m_m ≫ φ = τ^n_{φ(m)n}` and applying `Lf_{τ^n_{φ(m)n}}^* α`. -/
def ofCocycleTransitionIso (K0 : RingedSite.Hom.ModuleDerived.{w} (X ⦋0⦌))
    (α : (fHom (SimplexCategory.δ (1 : Fin 2))).modulePullbackDerived.obj K0 ≅
      (fHom (SimplexCategory.δ (0 : Fin 2))).modulePullbackDerived.obj K0)
    {m n : SimplexCategory} (φ : m ⟶ n) :
    (fHom φ).modulePullbackDerived.obj (ofCocycleObj X fHom K0 m) ≅ ofCocycleObj X fHom K0 n :=
  (ToposHom.DerivedPullbackComposition.compComparisonIso
      (fHom φ) (fHom (CategoryTheory.SimplicialSites.Sheaf.vertexOp m)) (fHom ((CategoryTheory.SimplicialSites.Sheaf.vertexOp m) ≫ φ))
      (functoriality.pullbackCompIso (CategoryTheory.SimplicialSites.Sheaf.vertexOp m) φ)).app K0 ≪≫
    (recodePullback X fHom
      (SimplexCategory.Hom.ext_zero_left (CategoryTheory.SimplicialSites.Sheaf.vertexOp m ≫ φ)
        (SimplexCategory.δ (1 : Fin 2) ≫ CategoryTheory.SimplicialSites.Sheaf.edgeOp φ))).app K0 ≪≫
    (ToposHom.DerivedPullbackComposition.compComparisonIso
      (fHom (CategoryTheory.SimplicialSites.Sheaf.edgeOp φ)) (fHom (SimplexCategory.δ (1 : Fin 2))) (fHom ((SimplexCategory.δ (1 : Fin 2)) ≫ (CategoryTheory.SimplicialSites.Sheaf.edgeOp φ)))
      (functoriality.pullbackCompIso (SimplexCategory.δ (1 : Fin 2)) (CategoryTheory.SimplicialSites.Sheaf.edgeOp φ))).symm.app K0 ≪≫
    (fHom (CategoryTheory.SimplicialSites.Sheaf.edgeOp φ)).modulePullbackDerived.mapIso α ≪≫
    (ToposHom.DerivedPullbackComposition.compComparisonIso
      (fHom (CategoryTheory.SimplicialSites.Sheaf.edgeOp φ)) (fHom (SimplexCategory.δ (0 : Fin 2))) (fHom ((SimplexCategory.δ (0 : Fin 2)) ≫ (CategoryTheory.SimplicialSites.Sheaf.edgeOp φ)))
      (functoriality.pullbackCompIso (SimplexCategory.δ (0 : Fin 2)) (CategoryTheory.SimplicialSites.Sheaf.edgeOp φ))).app K0 ≪≫
    (recodePullback X fHom
      (SimplexCategory.Hom.ext_zero_left
        (SimplexCategory.δ (0 : Fin 2) ≫ CategoryTheory.SimplicialSites.Sheaf.edgeOp φ)
        (CategoryTheory.SimplicialSites.Sheaf.vertexOp n))).app K0

/-- The forward map of `ofCocycleTransitionIso` is the edge-pullback composite for `K_φ`. -/
theorem ofCocycleTransitionIso_hom (K0 : RingedSite.Hom.ModuleDerived.{w} (X ⦋0⦌))
    (α : (fHom (SimplexCategory.δ (1 : Fin 2))).modulePullbackDerived.obj K0 ≅
      (fHom (SimplexCategory.δ (0 : Fin 2))).modulePullbackDerived.obj K0)
    {m n : SimplexCategory} (φ : m ⟶ n) :
    (ofCocycleTransitionIso X fHom functoriality K0 α φ).hom =
      ((ToposHom.DerivedPullbackComposition.compComparisonIso
      (fHom φ) (fHom (CategoryTheory.SimplicialSites.Sheaf.vertexOp m)) (fHom ((CategoryTheory.SimplicialSites.Sheaf.vertexOp m) ≫ φ))
      (functoriality.pullbackCompIso (CategoryTheory.SimplicialSites.Sheaf.vertexOp m) φ)).app K0 ≪≫
        (recodePullback X fHom
          (SimplexCategory.Hom.ext_zero_left (CategoryTheory.SimplicialSites.Sheaf.vertexOp m ≫ φ)
            (SimplexCategory.δ (1 : Fin 2) ≫ CategoryTheory.SimplicialSites.Sheaf.edgeOp φ))).app K0 ≪≫
        (ToposHom.DerivedPullbackComposition.compComparisonIso
      (fHom (CategoryTheory.SimplicialSites.Sheaf.edgeOp φ)) (fHom (SimplexCategory.δ (1 : Fin 2))) (fHom ((SimplexCategory.δ (1 : Fin 2)) ≫ (CategoryTheory.SimplicialSites.Sheaf.edgeOp φ)))
      (functoriality.pullbackCompIso (SimplexCategory.δ (1 : Fin 2)) (CategoryTheory.SimplicialSites.Sheaf.edgeOp φ))).symm.app K0 ≪≫
        (fHom (CategoryTheory.SimplicialSites.Sheaf.edgeOp φ)).modulePullbackDerived.mapIso α ≪≫
        (ToposHom.DerivedPullbackComposition.compComparisonIso
      (fHom (CategoryTheory.SimplicialSites.Sheaf.edgeOp φ)) (fHom (SimplexCategory.δ (0 : Fin 2))) (fHom ((SimplexCategory.δ (0 : Fin 2)) ≫ (CategoryTheory.SimplicialSites.Sheaf.edgeOp φ)))
      (functoriality.pullbackCompIso (SimplexCategory.δ (0 : Fin 2)) (CategoryTheory.SimplicialSites.Sheaf.edgeOp φ))).app K0 ≪≫
        (recodePullback X fHom
          (SimplexCategory.Hom.ext_zero_left
            (SimplexCategory.δ (0 : Fin 2) ≫ CategoryTheory.SimplicialSites.Sheaf.edgeOp φ)
            (CategoryTheory.SimplicialSites.Sheaf.vertexOp n))).app K0).hom :=
  rfl

end RingedSite.Simplicial.DerivedModuleSystem

namespace CategoryTheory.SimplicialSites.DerivedModuleSystem

open RingedSite.Simplicial.DerivedModuleSystem

variable (C : SimplexCategory ⥤ Cat.{v, u}) (J : ∀ n, Precoverage (C.obj n))
variable [∀ n, HasWeakSheafify (J n).toGrothendieck (Type w)]
variable [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (C.obj m)ᵒᵖ ⥤ Type w),
    ((C.map φ).toFunctor).op.HasLeftKanExtension P]
variable [IsMorphismDiagram.{u, v, w} C J]
variable (O : Sheaf (topology C J) RingCat.{w})
variable [(topology C J).HasSheafCompose (forget RingCat.{w})]
variable [∀ n, ((J n).toGrothendieck).HasSheafCompose (forget RingCat.{w})]
variable [UnivLE.{max u v, w}]
variable [∀ {m n : SimplexCategory} (φ : m ⟶ n),
    (SheafOfModules.restrictScalars.{w}
      (ringedToposMap C J O φ).structureMap).IsRightAdjoint]
variable [∀ {m n : SimplexCategory} (φ : m ⟶ n),
    ToposHom.HasModulePullbackDerived (ringedToposMap C J O φ)]


/-- Transitions of the cocycle system respect composition of simplex operators after the
canonical comparison `Lf_φ^* ∘ Lf_ψ^* ⟶ Lf_{ψ ≫ φ}^*`. -/
theorem ofCocycleOnComponents_map_comp (K0 : RingedSite.Hom.ModuleDerived.{w} (componentRingedSite C J O ⦋0⦌))
    (α : (ringedToposMap C J O (SimplexCategory.δ (1 : Fin 2))).modulePullbackDerived.obj K0 ≅
      (ringedToposMap C J O (SimplexCategory.δ (0 : Fin 2))).modulePullbackDerived.obj K0)
    (h : cocycleLeft (fun n ↦ componentRingedSite C J O n) (fun φ ↦ ringedToposMap C J O φ) (modulePullbackFunctoriality C J O) α =
      cocycleRight (fun n ↦ componentRingedSite C J O n) (fun φ ↦ ringedToposMap C J O φ) (modulePullbackFunctoriality C J O) α)
    {l m n : SimplexCategory} (ψ : l ⟶ m) (φ : m ⟶ n) :
    (derivedPullbackCompComparisonOf (ringedToposMap C J O φ) (ringedToposMap C J O ψ) (ringedToposMap C J O (ψ ≫ φ))
        ((modulePullbackFunctoriality C J O).pullbackCompIso ψ φ)).app (ofCocycleObj (fun n ↦ componentRingedSite C J O n) (fun φ ↦ ringedToposMap C J O φ) K0 l) ≫
      (ofCocycleTransitionIso (fun n ↦ componentRingedSite C J O n) (fun φ ↦ ringedToposMap C J O φ) (modulePullbackFunctoriality C J O) K0 α (ψ ≫ φ)).hom =
      (ringedToposMap C J O φ).modulePullbackDerived.map (ofCocycleTransitionIso (fun n ↦ componentRingedSite C J O n) (fun φ ↦ ringedToposMap C J O φ) (modulePullbackFunctoriality C J O) K0 α ψ).hom ≫
        (ofCocycleTransitionIso (fun n ↦ componentRingedSite C J O n) (fun φ ↦ ringedToposMap C J O φ) (modulePullbackFunctoriality C J O) K0 α φ).hom :=
  sorry


/-- The last-vertex derived pullbacks with the edge-pullback transitions form a simplicial system. -/
def ofCocycleOnComponents (K0 : RingedSite.Hom.ModuleDerived.{w} (componentRingedSite C J O ⦋0⦌))
    (α : (ringedToposMap C J O (SimplexCategory.δ (1 : Fin 2))).modulePullbackDerived.obj K0 ≅
      (ringedToposMap C J O (SimplexCategory.δ (0 : Fin 2))).modulePullbackDerived.obj K0)
    (h : cocycleLeft (fun n ↦ componentRingedSite C J O n) (fun φ ↦ ringedToposMap C J O φ) (modulePullbackFunctoriality C J O) α =
      cocycleRight (fun n ↦ componentRingedSite C J O n) (fun φ ↦ ringedToposMap C J O φ) (modulePullbackFunctoriality C J O) α) :
    RingedSite.Simplicial.DerivedModuleSystem (fun n ↦ componentRingedSite C J O n) (fun φ ↦ ringedToposMap C J O φ) (modulePullbackFunctoriality C J O) :=
  RingedSite.Simplicial.DerivedModuleSystem.of (modulePullbackFunctoriality C J O)
    (ofCocycleObj (fun n ↦ componentRingedSite C J O n) (fun φ ↦ ringedToposMap C J O φ) K0)
    (fun φ ↦ (ofCocycleTransitionIso (fun n ↦ componentRingedSite C J O n) (fun φ ↦ ringedToposMap C J O φ) (modulePullbackFunctoriality C J O) K0 α φ).hom)
    (ofCocycleOnComponents_map_comp C J O K0 α h)

/-- The object in each degree is the derived pullback along its last vertex. -/
theorem ofCocycleOnComponents_obj (K0 : RingedSite.Hom.ModuleDerived.{w} (componentRingedSite C J O ⦋0⦌))
    (α : (ringedToposMap C J O (SimplexCategory.δ (1 : Fin 2))).modulePullbackDerived.obj K0 ≅
      (ringedToposMap C J O (SimplexCategory.δ (0 : Fin 2))).modulePullbackDerived.obj K0)
    (h : cocycleLeft (fun n ↦ componentRingedSite C J O n) (fun φ ↦ ringedToposMap C J O φ) (modulePullbackFunctoriality C J O) α =
      cocycleRight (fun n ↦ componentRingedSite C J O n) (fun φ ↦ ringedToposMap C J O φ) (modulePullbackFunctoriality C J O) α) (n : SimplexCategory) :
    (ofCocycleOnComponents C J O K0 α h).obj n =
      ofCocycleObj (fun n ↦ componentRingedSite C J O n) (fun φ ↦ ringedToposMap C J O φ) K0 n := rfl

/-- The transition along a simplex operator is the prescribed edge-pullback composite. -/
theorem ofCocycleOnComponents_map (K0 : RingedSite.Hom.ModuleDerived.{w} (componentRingedSite C J O ⦋0⦌))
    (α : (ringedToposMap C J O (SimplexCategory.δ (1 : Fin 2))).modulePullbackDerived.obj K0 ≅
      (ringedToposMap C J O (SimplexCategory.δ (0 : Fin 2))).modulePullbackDerived.obj K0)
    (h : cocycleLeft (fun n ↦ componentRingedSite C J O n) (fun φ ↦ ringedToposMap C J O φ) (modulePullbackFunctoriality C J O) α =
      cocycleRight (fun n ↦ componentRingedSite C J O n) (fun φ ↦ ringedToposMap C J O φ) (modulePullbackFunctoriality C J O) α) {m n : SimplexCategory} (φ : m ⟶ n) :
    (ofCocycleOnComponents C J O K0 α h).map φ =
      (ofCocycleTransitionIso (fun n ↦ componentRingedSite C J O n) (fun φ ↦ ringedToposMap C J O φ) (modulePullbackFunctoriality C J O) K0 α φ).hom := rfl

/-- Every transition of the system obtained from a coface cocycle is an isomorphism. -/
theorem ofCocycleOnComponents_isCartesian (K0 : RingedSite.Hom.ModuleDerived.{w} (componentRingedSite C J O ⦋0⦌))
    (α : (ringedToposMap C J O (SimplexCategory.δ (1 : Fin 2))).modulePullbackDerived.obj K0 ≅
      (ringedToposMap C J O (SimplexCategory.δ (0 : Fin 2))).modulePullbackDerived.obj K0)
    (h : cocycleLeft (fun n ↦ componentRingedSite C J O n) (fun φ ↦ ringedToposMap C J O φ) (modulePullbackFunctoriality C J O) α =
      cocycleRight (fun n ↦ componentRingedSite C J O n) (fun φ ↦ ringedToposMap C J O φ) (modulePullbackFunctoriality C J O) α) :

    RingedSite.Simplicial.DerivedModuleSystem.IsCartesian
      (ofCocycleOnComponents C J O K0 α h) := sorry

end CategoryTheory.SimplicialSites.DerivedModuleSystem
