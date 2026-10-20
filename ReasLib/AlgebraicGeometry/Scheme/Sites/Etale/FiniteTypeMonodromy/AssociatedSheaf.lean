/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.FiniteTypeMonodromy.Basic
public import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction
public import Mathlib.CategoryTheory.Sites.Point.Skyscraper

/-!
# Sheaves associated to discrete linear monodromy

Equivariant functions on geometric finite fibers form a module presheaf on
finite étale schemes. Left Kan extension and sheafification realize this
presheaf on the small étale site.
-/

public section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Action.ModuleCat Opposite
open scoped FintypeCatDiscrete

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.FiniteTypeMonodromy.AssociatedSheaf

variable {X : Scheme.{u}} [IrreducibleSpace X]
variable (Λ : Type (u + 1)) [Ring Λ] (xbar : GeometricPoint X)

/-- Equivariant functions from a geometric finite fiber to a linear representation
form a submodule of the module of all functions. -/
def sections (M : DiscreteModuleCat Λ (Aut (GeometricPoint.finiteFiber xbar)))
    (U : FiniteEtale X) : Submodule Λ ((GeometricPoint.finiteFiber xbar).obj U → M.obj.V) where
  carrier := {φ | ∀ (σ : Aut (GeometricPoint.finiteFiber xbar)) p,
    φ (σ.hom.app U p) = (M.obj.ρ σ).hom (φ p)}
  zero_mem' := by intro σ p; exact (M.obj.ρ σ).hom.map_zero.symm
  add_mem' := by
    intro φ ψ hφ hψ σ p
    exact (congrArg₂ (· + ·) (hφ σ p) (hψ σ p)).trans
      ((M.obj.ρ σ).hom.map_add _ _).symm
  smul_mem' := by
    intro a φ hφ σ p
    exact (congrArg (a • ·) (hφ σ p)).trans ((M.obj.ρ σ).hom.map_smul a _).symm

/-- Restriction of equivariant functions is precomposition with the finite fiber map. -/
def restrict (M : DiscreteModuleCat Λ (Aut (GeometricPoint.finiteFiber xbar)))
    {U V : FiniteEtale X} (f : U ⟶ V) :
    sections Λ xbar M V →ₗ[Λ] sections Λ xbar M U where
  toFun φ := ⟨fun p ↦ φ.val ((GeometricPoint.finiteFiber xbar).map f p), by
    intro σ p
    dsimp
    rw [← NatTrans.naturality_apply σ.hom f p]
    exact φ.property σ _⟩
  map_add' φ ψ := rfl
  map_smul' a φ := rfl

/-- Equivariant functions on finite étale fibers, with pullback as restriction. -/
def presheaf (M : DiscreteModuleCat Λ (Aut (GeometricPoint.finiteFiber xbar))) :
    (FiniteEtale X)ᵒᵖ ⥤ ModuleCat.{u + 1} Λ where
  obj U := ModuleCat.of Λ (sections Λ xbar M U.unop)
  map f := ModuleCat.ofHom (restrict Λ xbar M f.unop)
  map_id U := by ext φ p; simp [restrict]
  map_comp f g := by ext φ p; simp [restrict]

/-- An equivariant linear map acts pointwise on equivariant sections. -/
def sectionsMap {M N : DiscreteModuleCat Λ (Aut (GeometricPoint.finiteFiber xbar))}
    (f : M ⟶ N) (U : FiniteEtale X) : sections Λ xbar M U →ₗ[Λ] sections Λ xbar N U where
  toFun φ := ⟨fun p ↦ f.hom.hom (φ.val p), by
    intro σ p
    dsimp
    rw [φ.property σ p]
    exact congrArg (fun k ↦ k (φ.val p)) (f.hom.comm σ)⟩
  map_add' φ ψ := by ext p; exact f.hom.hom.hom.map_add _ _
  map_smul' a φ := by ext p; exact f.hom.hom.hom.map_smul a _

/-- Discrete linear representations give a functor to finite-étale module presheaves. -/
def presheafFunctor :
    DiscreteModuleCat Λ (Aut (GeometricPoint.finiteFiber xbar)) ⥤
      ((FiniteEtale X)ᵒᵖ ⥤ ModuleCat.{u + 1} Λ) where
  obj := presheaf Λ xbar
  map f :=
    { app U := ModuleCat.ofHom (sectionsMap Λ xbar f U.unop)
      naturality := by intro U V g; ext φ; rfl }
  map_id M := by ext U φ; rfl
  map_comp f g := by ext U φ; rfl

variable [HasWeakSheafify X.smallEtaleTopology (ModuleCat.{u + 1} Λ)]
variable [∀ U : X.Etale,
  HasWeakSheafify (X.smallEtaleTopology.over U) (ModuleCat.{u + 1} Λ)]

/-- The associated sheaf functor extends equivariant sections to the small étale
site and sheafifies the resulting module presheaf. -/
def sheafFunctor :
    DiscreteModuleCat Λ (Aut (GeometricPoint.finiteFiber xbar)) ⥤
      Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ) :=
  presheafFunctor Λ xbar ⋙ (FiniteEtale.toEtale X).op.lan ⋙
    presheafToSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)

/-- Finite generation and continuity of monodromy make the associated sheaf
locally constant of finite type. -/
theorem isFiniteTypeLocallyConstant
    (M : (finiteTypeDiscreteModule Λ (Aut (GeometricPoint.finiteFiber xbar))).FullSubcategory) :
    Sheaf.IsFiniteTypeLocallyConstantModule ((sheafFunctor Λ xbar).obj M.obj) := sorry

/-- A finitely generated discrete representation determines a finite-type locally
constant module sheaf. -/
def functor :
    (finiteTypeDiscreteModule Λ (Aut (GeometricPoint.finiteFiber xbar))).FullSubcategory ⥤
      (Sheaf.finiteTypeLocallyConstantModule X.smallEtaleTopology Λ).FullSubcategory :=
  (Sheaf.finiteTypeLocallyConstantModule X.smallEtaleTopology Λ).lift
    ((finiteTypeDiscreteModule Λ (Aut (GeometricPoint.finiteFiber xbar))).ι ⋙
      sheafFunctor Λ xbar) (isFiniteTypeLocallyConstant Λ xbar)

variable (huni : X.isGeometricallyUnibranch)

/-- The linear map from the regular module with specified value at one. -/
private def sectionLinear (A : ModuleCat.{u + 1} Λ) (t : A) : ModuleCat.of Λ Λ ⟶ A :=
  ModuleCat.ofHom
    { toFun := fun a ↦ a • t
      map_add' := fun a b ↦ add_smul a b t
      map_smul' := fun a b ↦ mul_smul a b t }

/-- Representatives of an equivariant germ function consist of a finite étale
map and an actual section whose germs equal the prescribed function. -/
private abbrev unitInvRepresentatives
    (F : (Sheaf.finiteTypeLocallyConstantModule X.smallEtaleTopology Λ).FullSubcategory)
    (U : FiniteEtale X)
    (φ : sections Λ xbar (discretePi1ModuleOfFiniteTypeLocallyConstantSheaf Λ xbar F) U) :=
  Σ W : FiniteEtale X, Σ f : W ⟶ U,
    {t : F.obj.obj.obj (op ((FiniteEtale.toEtale X).obj W)) //
      ∀ q : (GeometricPoint.finiteFiber xbar).obj W,
        colimit.ι (StalkRepresentation.diagram Λ xbar F.obj.obj) (op ⟨W, q⟩) t =
          φ.val ((GeometricPoint.finiteFiber xbar).map f q)}

/-- Each matching representative maps its finite étale domain into the target. -/
private def unitInvArrow
    (F : (Sheaf.finiteTypeLocallyConstantModule X.smallEtaleTopology Λ).FullSubcategory)
    (U : FiniteEtale X)
    (φ : sections Λ xbar (discretePi1ModuleOfFiniteTypeLocallyConstantSheaf Λ xbar F) U)
    (i : unitInvRepresentatives Λ xbar F U φ) :
    (FiniteEtale.toEtale X).obj i.1 ⟶ (FiniteEtale.toEtale X).obj U :=
  (FiniteEtale.toEtale X).map i.2.1

include huni in
/-- The finite étale domains of all matching section representatives cover the
target finite étale object. -/
private theorem unitInv_covering
    (F : (Sheaf.finiteTypeLocallyConstantModule X.smallEtaleTopology Λ).FullSubcategory)
    (U : FiniteEtale X)
    (φ : sections Λ xbar (discretePi1ModuleOfFiniteTypeLocallyConstantSheaf Λ xbar F) U) :
    Sieve.ofArrows (fun i : unitInvRepresentatives Λ xbar F U φ ↦
      (FiniteEtale.toEtale X).obj i.1) (unitInvArrow Λ xbar F U φ) ∈
        X.smallEtaleTopology ((FiniteEtale.toEtale X).obj U) := sorry

include huni in
/-- Matching section representatives agree after restriction to every common
small étale test object over their finite étale target. -/
private theorem unitInv_compatible
    (F : (Sheaf.finiteTypeLocallyConstantModule X.smallEtaleTopology Λ).FullSubcategory)
    (U : FiniteEtale X)
    (φ : sections Λ xbar (discretePi1ModuleOfFiniteTypeLocallyConstantSheaf Λ xbar F) U)
    {V : X.Etale} {i j : unitInvRepresentatives Λ xbar F U φ}
    (a : V ⟶ (FiniteEtale.toEtale X).obj i.1)
    (b : V ⟶ (FiniteEtale.toEtale X).obj j.1)
    (hab : a ≫ unitInvArrow Λ xbar F U φ i = b ≫ unitInvArrow Λ xbar F U φ j) :
    F.obj.obj.map a.op i.2.2.val = F.obj.obj.map b.op j.2.2.val := sorry

/-- A matching germ function descends to a section by the unique sheaf
amalgamation of its actual section representatives. -/
private def unitInvSection
    (F : (Sheaf.finiteTypeLocallyConstantModule X.smallEtaleTopology Λ).FullSubcategory)
    (U : FiniteEtale X)
    (φ : sections Λ xbar (discretePi1ModuleOfFiniteTypeLocallyConstantSheaf Λ xbar F) U) :
    F.obj.obj.obj (op ((FiniteEtale.toEtale X).obj U)) :=
  (F.obj.property.amalgamateOfArrows (unitInvArrow Λ xbar F U φ)
    (unitInv_covering Λ xbar huni F U φ)
    (fun i ↦ sectionLinear Λ _ i.2.2.val)
    (by
      intro V i j a b hab
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro c
      change F.obj.obj.map a.op (c • i.2.2.val) = F.obj.obj.map b.op (c • j.2.2.val)
      rw [(F.obj.obj.map a.op).hom.map_smul,
        (F.obj.obj.map b.op).hom.map_smul, unitInv_compatible Λ xbar huni F U φ a b hab])) 1

/-- The descended section restricts to each of its specified representatives. -/
private theorem unitInvSection_representative
    (F : (Sheaf.finiteTypeLocallyConstantModule X.smallEtaleTopology Λ).FullSubcategory)
    (U : FiniteEtale X)
    (φ : sections Λ xbar (discretePi1ModuleOfFiniteTypeLocallyConstantSheaf Λ xbar F) U)
    (i : unitInvRepresentatives Λ xbar F U φ) :
    F.obj.obj.map (unitInvArrow Λ xbar F U φ i).op (unitInvSection Λ xbar huni F U φ) =
      i.2.2.val := by
  have h := F.obj.property.amalgamateOfArrows_map (unitInvArrow Λ xbar F U φ)
    (unitInv_covering Λ xbar huni F U φ)
    (fun i ↦ sectionLinear Λ _ i.2.2.val)
    (by
      intro V i j a b hab
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro c
      change F.obj.obj.map a.op (c • i.2.2.val) = F.obj.obj.map b.op (c • j.2.2.val)
      rw [(F.obj.obj.map a.op).hom.map_smul,
        (F.obj.obj.map b.op).hom.map_smul, unitInv_compatible Λ xbar huni F U φ a b hab]) i
  exact (congrArg (fun f : ModuleCat.of Λ Λ ⟶ _ ↦ f.hom (1 : Λ)) h).trans
    (one_smul Λ i.2.2.val)

/-- Reverse descent is additive and linear over the coefficient ring. -/
private theorem unitInv_isLinear
    (F : (Sheaf.finiteTypeLocallyConstantModule X.smallEtaleTopology Λ).FullSubcategory)
    (U : FiniteEtale X) :
    (∀ φ ψ, unitInvSection Λ xbar huni F U (φ + ψ) =
      unitInvSection Λ xbar huni F U φ + unitInvSection Λ xbar huni F U ψ) ∧
    (∀ (a : Λ) φ, unitInvSection Λ xbar huni F U (a • φ) =
      a • unitInvSection Λ xbar huni F U φ) := sorry

/-- Reverse descent commutes with restriction along finite étale maps. -/
private theorem unitInv_restrict
    (F : (Sheaf.finiteTypeLocallyConstantModule X.smallEtaleTopology Λ).FullSubcategory)
    {U V : FiniteEtale X} (f : U ⟶ V)
    (φ : sections Λ xbar (discretePi1ModuleOfFiniteTypeLocallyConstantSheaf Λ xbar F) V) :
    F.obj.obj.map ((FiniteEtale.toEtale X).map f).op (unitInvSection Λ xbar huni F V φ) =
      unitInvSection Λ xbar huni F U (restrict Λ xbar _ f φ) := sorry

/-- Reverse descent gives a natural linear map on the finite étale site. -/
private def unitInvFinite
    (F : (Sheaf.finiteTypeLocallyConstantModule X.smallEtaleTopology Λ).FullSubcategory) :
    presheaf Λ xbar (discretePi1ModuleOfFiniteTypeLocallyConstantSheaf Λ xbar F) ⟶
      (FiniteEtale.toEtale X).op ⋙ F.obj.obj where
  app U := ModuleCat.ofHom
    { toFun := unitInvSection Λ xbar huni F U.unop
      map_add' := (unitInv_isLinear Λ xbar huni F U.unop).1
      map_smul' := (unitInv_isLinear Λ xbar huni F U.unop).2 }
  naturality := by
    intro U V f
    ext φ
    exact (unitInv_restrict Λ xbar huni F f.unop φ).symm

/-- The reverse comparison extends finite étale descent through the Kan-extension
and sheafification adjunctions. -/
private def unitInvSheaf
    (F : (Sheaf.finiteTypeLocallyConstantModule X.smallEtaleTopology Λ).FullSubcategory) :
    (sheafFunctor Λ xbar).obj (discretePi1ModuleOfFiniteTypeLocallyConstantSheaf Λ xbar F) ⟶
      F.obj :=
  ((sheafificationAdjunction X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).homEquiv _ F.obj).symm
    ((((FiniteEtale.toEtale X).op.lanAdjunction (ModuleCat.{u + 1} Λ)).homEquiv _ _).symm
      (unitInvFinite Λ xbar huni F))

/-- A finite étale equivariant section maps to the associated sheaf by the units
of Kan extension and sheafification. -/
private def insert
    (M : DiscreteModuleCat Λ (Aut (GeometricPoint.finiteFiber xbar))) (U : FiniteEtale X) :
    (presheaf Λ xbar M).obj (op U) ⟶
      ((sheafFunctor Λ xbar).obj M).obj.obj (op ((FiniteEtale.toEtale X).obj U)) :=
  ((FiniteEtale.toEtale X).op.lanUnit.app (presheaf Λ xbar M)).app (op U) ≫
    (toSheafify X.smallEtaleTopology
      ((FiniteEtale.toEtale X).op.lan.obj (presheaf Λ xbar M))).app
        (op ((FiniteEtale.toEtale X).obj U))

/-- A section on a finite étale object determines its equivariant function of
finite-neighborhood germs. -/
private def sectionGerms
    (F : (Sheaf.finiteTypeLocallyConstantModule X.smallEtaleTopology Λ).FullSubcategory)
    (W : FiniteEtale X) (t : F.obj.obj.obj (op ((FiniteEtale.toEtale X).obj W))) :
    sections Λ xbar (discretePi1ModuleOfFiniteTypeLocallyConstantSheaf Λ xbar F) W :=
  ⟨fun q ↦ colimit.ι (StalkRepresentation.diagram Λ xbar F.obj.obj) (op ⟨W, q⟩) t, by
    intro σ q
    exact (congrArg (fun f ↦ f t)
      (StalkRepresentation.ι_finiteAction Λ xbar F.obj.obj σ (op ⟨W, q⟩))).symm⟩

/-- Local finite étale representatives of a section consist of actual common
small étale charts on which the section is the restriction of a finite étale section. -/
private abbrev unitRepresentatives
    (F : (Sheaf.finiteTypeLocallyConstantModule X.smallEtaleTopology Λ).FullSubcategory)
    (U : X.Etale) (s : F.obj.obj.obj (op U)) :=
  Σ V : X.Etale, Σ W : FiniteEtale X, Σ a : V ⟶ U,
    Σ b : V ⟶ (FiniteEtale.toEtale X).obj W,
      {t : F.obj.obj.obj (op ((FiniteEtale.toEtale X).obj W)) //
        F.obj.obj.map a.op s = F.obj.obj.map b.op t}

/-- The local chart of a finite étale representative maps to the test object. -/
private def unitArrow
    (F : (Sheaf.finiteTypeLocallyConstantModule X.smallEtaleTopology Λ).FullSubcategory)
    (U : X.Etale) (s : F.obj.obj.obj (op U)) (i : unitRepresentatives Λ F U s) : i.1 ⟶ U :=
  i.2.2.1

/-- A local finite étale section determines an actual local section of the
associated sheaf by insertion of its equivariant germ function. -/
private def unitLocalSection
    (F : (Sheaf.finiteTypeLocallyConstantModule X.smallEtaleTopology Λ).FullSubcategory)
    (U : X.Etale) (s : F.obj.obj.obj (op U)) (i : unitRepresentatives Λ F U s) :
    ((sheafFunctor Λ xbar).obj
      (discretePi1ModuleOfFiniteTypeLocallyConstantSheaf Λ xbar F)).obj.obj (op i.1) :=
  ((sheafFunctor Λ xbar).obj
    (discretePi1ModuleOfFiniteTypeLocallyConstantSheaf Λ xbar F)).obj.map i.2.2.2.1.op
      (insert Λ xbar _ i.2.1 (sectionGerms Λ xbar F i.2.1 i.2.2.2.2.val))

include huni in
/-- Every section of a finite-type locally constant sheaf is locally the
restriction of a section on a finite étale object. -/
private theorem unit_covering
    (F : (Sheaf.finiteTypeLocallyConstantModule X.smallEtaleTopology Λ).FullSubcategory)
    (U : X.Etale) (s : F.obj.obj.obj (op U)) :
    Sieve.ofArrows (fun i : unitRepresentatives Λ F U s ↦ i.1) (unitArrow Λ F U s) ∈
      X.smallEtaleTopology U := sorry

include huni in
/-- The inserted local germ sections agree on all common small étale overlaps. -/
private theorem unit_compatible
    (F : (Sheaf.finiteTypeLocallyConstantModule X.smallEtaleTopology Λ).FullSubcategory)
    (U : X.Etale) (s : F.obj.obj.obj (op U))
    {V : X.Etale} {i j : unitRepresentatives Λ F U s}
    (a : V ⟶ i.1) (b : V ⟶ j.1)
    (hab : a ≫ unitArrow Λ F U s i = b ≫ unitArrow Λ F U s j) :
    ((sheafFunctor Λ xbar).obj
      (discretePi1ModuleOfFiniteTypeLocallyConstantSheaf Λ xbar F)).obj.map a.op
        (unitLocalSection Λ xbar F U s i) =
    ((sheafFunctor Λ xbar).obj
      (discretePi1ModuleOfFiniteTypeLocallyConstantSheaf Λ xbar F)).obj.map b.op
        (unitLocalSection Λ xbar F U s j) := sorry

/-- Local finite étale germ sections glue uniquely to the forward comparison section. -/
private def unitHomSection
    (F : (Sheaf.finiteTypeLocallyConstantModule X.smallEtaleTopology Λ).FullSubcategory)
    (U : X.Etale) (s : F.obj.obj.obj (op U)) :
    ((sheafFunctor Λ xbar).obj
      (discretePi1ModuleOfFiniteTypeLocallyConstantSheaf Λ xbar F)).obj.obj (op U) :=
  (((sheafFunctor Λ xbar).obj
    (discretePi1ModuleOfFiniteTypeLocallyConstantSheaf Λ xbar F)).property.amalgamateOfArrows
    (unitArrow Λ F U s) (unit_covering Λ huni F U s)
    (fun i ↦ sectionLinear Λ _ (unitLocalSection Λ xbar F U s i))
    (by
      intro V i j a b hab
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro c
      change ((sheafFunctor Λ xbar).obj
        (discretePi1ModuleOfFiniteTypeLocallyConstantSheaf Λ xbar F)).obj.map a.op
          (c • unitLocalSection Λ xbar F U s i) =
        ((sheafFunctor Λ xbar).obj
        (discretePi1ModuleOfFiniteTypeLocallyConstantSheaf Λ xbar F)).obj.map b.op
          (c • unitLocalSection Λ xbar F U s j)
      rw [map_smul, map_smul, unit_compatible Λ xbar huni F U s a b hab])) 1

/-- Forward descent is additive and linear over the coefficient ring. -/
private theorem unitHom_isLinear
    (F : (Sheaf.finiteTypeLocallyConstantModule X.smallEtaleTopology Λ).FullSubcategory)
    (U : X.Etale) :
    (∀ s t, unitHomSection Λ xbar huni F U (s + t) =
      unitHomSection Λ xbar huni F U s + unitHomSection Λ xbar huni F U t) ∧
    (∀ (a : Λ) s, unitHomSection Λ xbar huni F U (a • s) =
      a • unitHomSection Λ xbar huni F U s) := sorry

/-- Forward descent commutes with restriction along arbitrary small étale maps. -/
private theorem unitHom_restrict
    (F : (Sheaf.finiteTypeLocallyConstantModule X.smallEtaleTopology Λ).FullSubcategory)
    {U V : X.Etale} (f : U ⟶ V) (s : F.obj.obj.obj (op V)) :
    ((sheafFunctor Λ xbar).obj
      (discretePi1ModuleOfFiniteTypeLocallyConstantSheaf Λ xbar F)).obj.map f.op
        (unitHomSection Λ xbar huni F V s) =
      unitHomSection Λ xbar huni F U (F.obj.obj.map f.op s) := sorry

/-- The forward sheaf comparison has the actual section function specified by descent. -/
private def unitHomSheaf
    (F : (Sheaf.finiteTypeLocallyConstantModule X.smallEtaleTopology Λ).FullSubcategory) :
    F.obj ⟶ (sheafFunctor Λ xbar).obj
      (discretePi1ModuleOfFiniteTypeLocallyConstantSheaf Λ xbar F) where
  hom :=
    { app U := ModuleCat.ofHom
        { toFun := unitHomSection Λ xbar huni F U.unop
          map_add' := (unitHom_isLinear Λ xbar huni F U.unop).1
          map_smul' := (unitHom_isLinear Λ xbar huni F U.unop).2 }
      naturality := by
        intro U V f
        ext s
        exact (unitHom_restrict Λ xbar huni F f.unop s).symm }

/-- Forward and reverse descent compose to the identity on the original sheaf. -/
private theorem unitHom_inv
    (F : (Sheaf.finiteTypeLocallyConstantModule X.smallEtaleTopology Λ).FullSubcategory) :
    unitHomSheaf Λ xbar huni F ≫ unitInvSheaf Λ xbar huni F = 𝟙 _ := sorry

/-- Reverse and forward descent compose to the identity on the associated sheaf. -/
private theorem unitInv_hom
    (F : (Sheaf.finiteTypeLocallyConstantModule X.smallEtaleTopology Λ).FullSubcategory) :
    unitInvSheaf Λ xbar huni F ≫ unitHomSheaf Λ xbar huni F = 𝟙 _ := sorry

/-- The comparison of a sheaf with the sheaf associated to its monodromy has
both directions given by specified descent operations. -/
private def unitApp
    (F : (Sheaf.finiteTypeLocallyConstantModule X.smallEtaleTopology Λ).FullSubcategory) :
    F ≅ ((finiteTypeLocallyConstantModuleToFinitePi1Modules Λ huni xbar) ⋙
      functor Λ xbar).obj F :=
  ObjectProperty.isoMk _
    { hom := unitHomSheaf Λ xbar huni F
      inv := unitInvSheaf Λ xbar huni F
      hom_inv_id := unitHom_inv Λ xbar huni F
      inv_hom_id := unitInv_hom Λ xbar huni F }

/-- Descent of finite-neighborhood germs is natural in the module sheaf. -/
private theorem unit_naturality
    {F G : (Sheaf.finiteTypeLocallyConstantModule X.smallEtaleTopology Λ).FullSubcategory}
    (f : F ⟶ G) :
    f ≫ (unitApp Λ xbar huni G).hom =
      (unitApp Λ xbar huni F).hom ≫
        ((finiteTypeLocallyConstantModuleToFinitePi1Modules Λ huni xbar) ⋙
          functor Λ xbar).map f := sorry

/-- The natural comparison from a sheaf to the sheaf associated to its monodromy. -/
def unitIso : 𝟭 _ ≅ finiteTypeLocallyConstantModuleToFinitePi1Modules Λ huni xbar ⋙
    functor Λ xbar :=
  NatIso.ofComponents (unitApp Λ xbar huni) (fun f ↦ unit_naturality Λ xbar huni f)

/-- Evaluation of equivariant functions gives a map to the restricted skyscraper
presheaf of the underlying module. -/
private def evaluationFinite
    (M : DiscreteModuleCat Λ (Aut (GeometricPoint.finiteFiber xbar))) :
    presheaf Λ xbar M ⟶ (FiniteEtale.toEtale X).op ⋙
      @GrothendieckTopology.Point.skyscraperPresheaf.{u, u + 1, u, u + 2, u + 1} _ _ _
        (GeometricPoint.toSmallEtalePoint xbar) (ModuleCat.{u + 1} Λ) _
        (fun β ↦ (ModuleCat.hasLimitsOfShape.{u, u, u + 1, u + 1} (J := Discrete β) :
          HasLimitsOfShape (Discrete β) (ModuleCat.{u + 1} Λ))) M.obj.V where
  app U := Pi.lift (fun q ↦ ModuleCat.ofHom
    { toFun := fun φ ↦ φ.val q
      map_add' := fun φ ψ ↦ rfl
      map_smul' := fun a φ ↦ rfl })
  naturality := by
    intro U V f
    apply limit.hom_ext
    intro q
    change (presheaf Λ xbar M).map f ≫ _ ≫ Pi.π _ q.as =
      _ ≫ Pi.map' _ _ ≫ Pi.π _ q.as
    rw [Pi.map'_comp_π]
    simp only [Category.comp_id, Pi.lift_π]
    ext φ
    rfl

/-- Finite étale evaluation extends through Kan extension and sheafification to
the skyscraper sheaf. -/
private def evaluationSheaf
    (M : DiscreteModuleCat Λ (Aut (GeometricPoint.finiteFiber xbar))) :
    (sheafFunctor Λ xbar).obj M ⟶
      @GrothendieckTopology.Point.skyscraperSheaf.{u, u + 1, u, u + 2, u + 1} _ _ _
        (GeometricPoint.toSmallEtalePoint xbar) (ModuleCat.{u + 1} Λ) _
        (fun β ↦ (ModuleCat.hasLimitsOfShape.{u, u, u + 1, u + 1} (J := Discrete β) :
          HasLimitsOfShape (Discrete β) (ModuleCat.{u + 1} Λ))) M.obj.V :=
  ((sheafificationAdjunction X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).homEquiv _ _).symm
    ((((FiniteEtale.toEtale X).op.lanAdjunction (ModuleCat.{u + 1} Λ)).homEquiv _ _).symm
      (evaluationFinite Λ xbar M))

/-- Evaluation of associated-sheaf germs in the coefficient module is the
skyscraper adjunct of finite étale evaluation. -/
private def counitHomFunction
    (M : DiscreteModuleCat Λ (Aut (GeometricPoint.finiteFiber xbar))) :
    (StalkRepresentation.finiteFiber Λ xbar).obj ((sheafFunctor Λ xbar).obj M).obj → M.obj.V :=
  (StalkRepresentation.germMap Λ xbar ((sheafFunctor Λ xbar).obj M) ≫
    ((@GrothendieckTopology.Point.skyscraperSheafAdjunction.{u, u + 1, u, u + 2, u + 1} _ _ _
      (GeometricPoint.toSmallEtalePoint xbar) (ModuleCat.{u + 1} Λ) _
      (fun β ↦ (ModuleCat.hasLimitsOfShape.{u, u, u + 1, u + 1} (J := Discrete β) :
          HasLimitsOfShape (Discrete β) (ModuleCat.{u + 1} Λ))) _).homEquiv _ _).symm
      (evaluationSheaf Λ xbar M)).hom

/-- The quotient of monodromy by the open stabilizer of a coefficient element
is an explicitly finite type. -/
private theorem orbit_finite
    (M : DiscreteModuleCat Λ (Aut (GeometricPoint.finiteFiber xbar))) (m : M.obj.V) :
    Finite (Aut (GeometricPoint.finiteFiber xbar) ⧸
      MulAction.stabilizer (Aut (GeometricPoint.finiteFiber xbar)) m) :=
  (MulAction.stabilizer (Aut (GeometricPoint.finiteFiber xbar)) m).quotient_finite_of_isOpen
    (M.property m)

/-- The finite orbit of a coefficient element, with its natural monodromy action. -/
private def orbitLarge
    (M : DiscreteModuleCat Λ (Aut (GeometricPoint.finiteFiber xbar))) (m : M.obj.V) :
    Action FintypeCat.{u + 1} (Aut (GeometricPoint.finiteFiber xbar)) :=
  Action.FintypeCat.ofMulAction _
    (@FintypeCat.of _ (orbit_finite Λ xbar M m))

/-- A universe-small realization of the finite orbit action. -/
private def orbitAction
    (M : DiscreteModuleCat Λ (Aut (GeometricPoint.finiteFiber xbar))) (m : M.obj.V) :
    Action FintypeCat.{u} (Aut (GeometricPoint.finiteFiber xbar)) :=
  (FintypeCat.uSwitch.mapAction _).obj (orbitLarge Λ xbar M m)

/-- The orbit realization maps injectively into the coefficient module. -/
private def orbitValue
    (M : DiscreteModuleCat Λ (Aut (GeometricPoint.finiteFiber xbar))) (m : M.obj.V)
    (p : (orbitAction Λ xbar M m).V) : M.obj.V :=
  MulAction.ofQuotientStabilizer _ m ((orbitLarge Λ xbar M m).V.uSwitchEquiv p)

/-- The coefficient value is injective on the finite orbit realization. -/
private theorem orbitValue_injective
    (M : DiscreteModuleCat Λ (Aut (GeometricPoint.finiteFiber xbar))) (m : M.obj.V) :
    Function.Injective (orbitValue Λ xbar M m) :=
  (MulAction.injective_ofQuotientStabilizer _ m).comp
    (orbitLarge Λ xbar M m).V.uSwitchEquiv.injective

/-- The value map from the finite orbit realization commutes with monodromy. -/
private theorem orbitValue_equivariant
    (M : DiscreteModuleCat Λ (Aut (GeometricPoint.finiteFiber xbar))) (m : M.obj.V)
    (σ : Aut (GeometricPoint.finiteFiber xbar)) (p : (orbitAction Λ xbar M m).V) :
    orbitValue Λ xbar M m (((orbitAction Λ xbar M m).ρ σ).hom p) =
      (M.obj.ρ σ).hom (orbitValue Λ xbar M m p) := by
  change MulAction.ofQuotientStabilizer _ m
    ((orbitLarge Λ xbar M m).V.uSwitchEquiv
      (FintypeCat.uSwitch.map ((orbitLarge Λ xbar M m).ρ σ) p)) = _
  rw [← FintypeCat.uSwitchEquiv_naturality]
  exact MulAction.ofQuotientStabilizer_smul _ m σ _

/-- Every stabilizer in a finite coefficient orbit is open, so its action is continuous. -/
private theorem orbitAction_continuous
    (M : DiscreteModuleCat Λ (Aut (GeometricPoint.finiteFiber xbar))) (m : M.obj.V) :
    (orbitAction Λ xbar M m).IsContinuous := by
  change ContinuousSMul (Aut (GeometricPoint.finiteFiber xbar)) (orbitAction Λ xbar M m).V
  apply continuousSMul_iff_stabilizer_isOpen.mpr
  intro p
  convert M.property (orbitValue Λ xbar M m p) using 1
  ext σ
  change (((orbitAction Λ xbar M m).ρ σ).hom p = p) ↔
    (M.obj.ρ σ).hom (orbitValue Λ xbar M m p) = orbitValue Λ xbar M m p
  rw [← orbitValue_equivariant Λ xbar M m σ p,
    (orbitValue_injective Λ xbar M m).eq_iff]

/-- The finite orbit is a continuous finite action. -/
private def orbitContinuous
    (M : DiscreteModuleCat Λ (Aut (GeometricPoint.finiteFiber xbar))) (m : M.obj.V) :
    ContAction FintypeCat.{u} (Aut (GeometricPoint.finiteFiber xbar)) :=
  ⟨orbitAction Λ xbar M m, orbitAction_continuous Λ xbar M m⟩

/-- The Galois-category inverse realizes a coefficient orbit by a finite étale object. -/
private def orbitCover
    (M : DiscreteModuleCat Λ (Aut (GeometricPoint.finiteFiber xbar))) (m : M.obj.V) :
    FiniteEtale X :=
  (GeometricPoint.fiberAction xbar).asEquivalence.inverse.obj (orbitContinuous Λ xbar M m)

/-- The fiber of the orbit cover is explicitly identified with its finite orbit action. -/
private def orbitFiberIso
    (M : DiscreteModuleCat Λ (Aut (GeometricPoint.finiteFiber xbar))) (m : M.obj.V) :
    (GeometricPoint.fiberAction xbar).obj (orbitCover Λ xbar M m) ≅
      orbitContinuous Λ xbar M m :=
  (GeometricPoint.fiberAction xbar).asEquivalence.counitIso.app (orbitContinuous Λ xbar M m)

/-- The finite étale orbit cover carries its actual equivariant coefficient section. -/
private def orbitSection
    (M : DiscreteModuleCat Λ (Aut (GeometricPoint.finiteFiber xbar))) (m : M.obj.V) :
    sections Λ xbar M (orbitCover Λ xbar M m) :=
  ⟨fun p ↦ orbitValue Λ xbar M m ((orbitFiberIso Λ xbar M m).hom.hom.hom p), by
    intro σ p
    have h := ConcreteCategory.congr_hom ((orbitFiberIso Λ xbar M m).hom.hom.comm σ) p
    change (orbitFiberIso Λ xbar M m).hom.hom.hom (σ.hom.app _ p) =
      ((orbitAction Λ xbar M m).ρ σ).hom ((orbitFiberIso Λ xbar M m).hom.hom.hom p) at h
    change orbitValue Λ xbar M m _ = _
    rw [h]
    exact orbitValue_equivariant Λ xbar M m σ _⟩

/-- The identity coset specifies the pointing of the finite étale orbit cover. -/
private def orbitPoint
    (M : DiscreteModuleCat Λ (Aut (GeometricPoint.finiteFiber xbar))) (m : M.obj.V) :
    (GeometricPoint.finiteFiber xbar).obj (orbitCover Λ xbar M m) :=
  (orbitFiberIso Λ xbar M m).inv.hom.hom
    ((orbitLarge Λ xbar M m).V.uSwitchEquiv.symm
      (QuotientGroup.mk (1 : Aut (GeometricPoint.finiteFiber xbar))))

/-- A coefficient element determines the germ of its actual section on its
pointed finite étale orbit cover. -/
private def counitInvFunction
    (M : DiscreteModuleCat Λ (Aut (GeometricPoint.finiteFiber xbar))) :
    M.obj.V → (StalkRepresentation.finiteFiber Λ xbar).obj ((sheafFunctor Λ xbar).obj M).obj :=
  fun m ↦ colimit.ι (StalkRepresentation.diagram Λ xbar ((sheafFunctor Λ xbar).obj M).obj)
    (op ⟨orbitCover Λ xbar M m, orbitPoint Λ xbar M m⟩)
      (insert Λ xbar M (orbitCover Λ xbar M m) (orbitSection Λ xbar M m))

/-- Evaluation of associated-sheaf germs is linear. -/
private theorem counitHom_isLinear
    (M : (finiteTypeDiscreteModule Λ (Aut (GeometricPoint.finiteFiber xbar))).FullSubcategory) :
    (∀ s t, counitHomFunction Λ xbar M.obj (s + t) =
      counitHomFunction Λ xbar M.obj s + counitHomFunction Λ xbar M.obj t) ∧
    (∀ (a : Λ) s, counitHomFunction Λ xbar M.obj (a • s) =
      a • counitHomFunction Λ xbar M.obj s) := sorry

/-- Taking the germ on a pointed orbit cover is linear in the coefficient element. -/
private theorem counitInv_isLinear
    (M : (finiteTypeDiscreteModule Λ (Aut (GeometricPoint.finiteFiber xbar))).FullSubcategory) :
    (∀ m n, counitInvFunction Λ xbar M.obj (m + n) =
      counitInvFunction Λ xbar M.obj m + counitInvFunction Λ xbar M.obj n) ∧
    (∀ (a : Λ) m, counitInvFunction Λ xbar M.obj (a • m) =
      a • counitInvFunction Λ xbar M.obj m) := sorry

/-- Evaluation of germs commutes with monodromy. -/
private theorem counitHom_equivariant
    (M : (finiteTypeDiscreteModule Λ (Aut (GeometricPoint.finiteFiber xbar))).FullSubcategory)
    (σ : Aut (GeometricPoint.finiteFiber xbar)) (s :
      (StalkRepresentation.finiteFiber Λ xbar).obj ((sheafFunctor Λ xbar).obj M.obj).obj) :
    counitHomFunction Λ xbar M.obj
      ((StalkRepresentation.finiteAction Λ xbar ((sheafFunctor Λ xbar).obj M.obj).obj σ).hom s) =
      (M.obj.obj.ρ σ).hom (counitHomFunction Λ xbar M.obj s) := sorry

/-- The pointed orbit-cover germ construction commutes with monodromy. -/
private theorem counitInv_equivariant
    (M : (finiteTypeDiscreteModule Λ (Aut (GeometricPoint.finiteFiber xbar))).FullSubcategory)
    (σ : Aut (GeometricPoint.finiteFiber xbar)) (m : M.obj.obj.V) :
    counitInvFunction Λ xbar M.obj ((M.obj.obj.ρ σ).hom m) =
      (StalkRepresentation.finiteAction Λ xbar ((sheafFunctor Λ xbar).obj M.obj).obj σ).hom
        (counitInvFunction Λ xbar M.obj m) := sorry

/-- Evaluation followed by the pointed orbit-cover construction preserves germs. -/
private theorem counitHom_inv
    (M : (finiteTypeDiscreteModule Λ (Aut (GeometricPoint.finiteFiber xbar))).FullSubcategory)
    (s : (StalkRepresentation.finiteFiber Λ xbar).obj ((sheafFunctor Λ xbar).obj M.obj).obj) :
    counitInvFunction Λ xbar M.obj (counitHomFunction Λ xbar M.obj s) = s := sorry

/-- The germ of the pointed orbit-cover section evaluates to its coefficient element. -/
private theorem counitInv_hom
    (M : (finiteTypeDiscreteModule Λ (Aut (GeometricPoint.finiteFiber xbar))).FullSubcategory)
    (m : M.obj.obj.V) :
    counitHomFunction Λ xbar M.obj (counitInvFunction Λ xbar M.obj m) = m := sorry

/-- The coefficient comparison isomorphism has specified evaluation and orbit-germ maps. -/
private def counitApp
    (M : (finiteTypeDiscreteModule Λ (Aut (GeometricPoint.finiteFiber xbar))).FullSubcategory) :
    ((functor Λ xbar) ⋙ finiteTypeLocallyConstantModuleToFinitePi1Modules Λ huni xbar).obj M ≅ M :=
  ObjectProperty.isoMk _ (ObjectProperty.isoMk _
    { hom :=
        { hom := ModuleCat.ofHom
            { toFun := counitHomFunction Λ xbar M.obj
              map_add' := (counitHom_isLinear Λ xbar M).1
              map_smul' := (counitHom_isLinear Λ xbar M).2 }
          comm := fun σ ↦ by ext s; exact counitHom_equivariant Λ xbar M σ s }
      inv :=
        { hom := ModuleCat.ofHom
            { toFun := counitInvFunction Λ xbar M.obj
              map_add' := (counitInv_isLinear Λ xbar M).1
              map_smul' := (counitInv_isLinear Λ xbar M).2 }
          comm := fun σ ↦ by ext m; exact counitInv_equivariant Λ xbar M σ m }
      hom_inv_id := by ext s; exact counitHom_inv Λ xbar M s
      inv_hom_id := by ext m; exact counitInv_hom Λ xbar M m })

/-- Evaluation and orbit-germ comparison are natural in coefficient morphisms. -/
private theorem counit_naturality
    {M N : (finiteTypeDiscreteModule Λ (Aut (GeometricPoint.finiteFiber xbar))).FullSubcategory}
    (f : M ⟶ N) :
    ((functor Λ xbar) ⋙ finiteTypeLocallyConstantModuleToFinitePi1Modules Λ huni xbar).map f ≫
      (counitApp Λ xbar huni N).hom = (counitApp Λ xbar huni M).hom ≫ f := sorry

/-- The associated-sheaf coefficient comparison is a natural isomorphism. -/
def counitIso : functor Λ xbar ⋙ finiteTypeLocallyConstantModuleToFinitePi1Modules Λ huni xbar ≅
    𝟭 _ :=
  NatIso.ofComponents (counitApp Λ xbar huni) (fun f ↦ counit_naturality Λ xbar huni f)

/-- The specified sheaf and coefficient comparison maps satisfy the triangle identity. -/
theorem triangle
    (F : (Sheaf.finiteTypeLocallyConstantModule X.smallEtaleTopology Λ).FullSubcategory) :
    (finiteTypeLocallyConstantModuleToFinitePi1Modules Λ huni xbar).map
      ((unitIso Λ xbar huni).hom.app F) ≫
        (counitIso Λ xbar huni).hom.app
          ((finiteTypeLocallyConstantModuleToFinitePi1Modules Λ huni xbar).obj F) = 𝟙 _ := sorry

end AlgebraicGeometry.Scheme.FiniteTypeMonodromy.AssociatedSheaf
