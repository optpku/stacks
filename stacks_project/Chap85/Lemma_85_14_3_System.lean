/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap85.Definition_85_14_1_System
public import stacks_project.Chap85.Lemma_85_12_4_Descent

/-!
# Cartesian derived-module systems from a coface cocycle

From `K_0` in `D(O_0)` and an isomorphism `α : Lf_{δ 1}^* K_0 ≅ Lf_{δ 0}^* K_0` in
`D(O_1)` satisfying the `C_2` cocycle, the vertex pullbacks
`K_n = Lf_{τ^n_n}^* K_0` and the source comparison maps `K_φ` assemble to a
cartesian simplicial system of the derived category of modules.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite Functor
open RingedSite
open scoped Simplicial
open ComplexShape

noncomputable section

universe u v w

namespace CategoryTheory.SimplicialSites.DerivedModuleSystem

section General

variable (X : SimplexCategory → RingedSite.{u, v, w})
variable [∀ n, (X n).siteTopology.HasSheafCompose (forget RingCat.{w})]
variable [UnivLE.{max u v, w}]
variable (fHom : ∀ {m n : SimplexCategory}, (m ⟶ n) → ToposHom (X n) (X m))
variable [∀ {m n : SimplexCategory} (φ : m ⟶ n),
    (SheafOfModules.restrictScalars.{w} (fHom φ).structureMap).IsRightAdjoint]
variable [∀ {m n : SimplexCategory} (φ : m ⟶ n),
    ToposHom.HasModulePullbackDerived (fHom φ)]
variable [functoriality : HasModulePullbackFunctoriality X fHom]

/-- Reidentify `Lf_φ^*` along an equality of simplex operators. -/
def recodePullback {m n : SimplexCategory} {φ ψ : m ⟶ n} (h : φ = ψ) :
    (fHom φ).modulePullbackDerived ≅ (fHom ψ).modulePullbackDerived :=
  eqToIso (congrArg (fun t : m ⟶ n ↦ (fHom t).modulePullbackDerived) h)

/-- `recodePullback` is the identity when the operator equality is `rfl`. -/
theorem recodePullback_refl {m n : SimplexCategory} (φ : m ⟶ n) :
    recodePullback X fHom (rfl : φ = φ) = Iso.refl _ :=
  sorry

/-- Homotopy-to-derived pullback along `f_{ψ ≫ φ}` identifies with the iterated homotopy-level
model of `f_ψ` then `f_φ`. -/
def compToDerivedIso {l m n : SimplexCategory} (ψ : l ⟶ m) (φ : m ⟶ n) :
    ToposHom.modulePullbackToDerived (fHom (ψ ≫ φ)) ≅
      (fHom ψ).modulePullback.mapHomotopyCategory (up ℤ) ⋙
        ToposHom.modulePullbackToDerived (fHom φ) :=
  derivedPullbackCompToDerivedIso (fHom φ) (fHom ψ) (fHom (ψ ≫ φ))
    (functoriality.pullbackCompIso ψ φ)

/-- Iterated homotopy-to-derived model of `f_ψ` then `f_φ`. -/
abbrev iteratedToDerived {l m n : SimplexCategory} (ψ : l ⟶ m) (φ : m ⟶ n) :
    Hom.ModuleHomotopy.{w} (X l) ⥤ Hom.ModuleDerived.{w} (X n) :=
  (fHom ψ).modulePullback.mapHomotopyCategory (up ℤ) ⋙
    ToposHom.modulePullbackToDerived (fHom φ)

/-- Existence of the total left derived functor of the iterated homotopy-level model, transported
along `compToDerivedIso`. -/
instance hasLeftDerivedFunctor_iteratedToDerived {l m n : SimplexCategory}
    (ψ : l ⟶ m) (φ : m ⟶ n) :
    (iteratedToDerived X fHom ψ φ).HasLeftDerivedFunctor (Hom.ModuleQis (X l)) :=
  (Functor.hasLeftDerivedFunctor_iff_of_iso (compToDerivedIso X fHom ψ φ)
    (Hom.ModuleQis (X l))).mp inferInstance

/-- Total left derived functor of the iterated homotopy-level model of `f_ψ` then `f_φ`. -/
abbrev iteratedDerived {l m n : SimplexCategory} (ψ : l ⟶ m) (φ : m ⟶ n) :
    Hom.ModuleDerived.{w} (X l) ⥤ Hom.ModuleDerived.{w} (X n) :=
  (iteratedToDerived X fHom ψ φ).totalLeftDerived
    (Hom.moduleLocalization (X l)) (Hom.ModuleQis (X l))

/-- Canonical isomorphism between the iterated total left derived functor and `Lf_{ψ ≫ φ}^*`. -/
def iteratedDerivedIso {l m n : SimplexCategory} (ψ : l ⟶ m) (φ : m ⟶ n) :
    iteratedDerived X fHom ψ φ ≅ (fHom (ψ ≫ φ)).modulePullbackDerived :=
  Functor.leftDerivedNatIso
    (iteratedDerived X fHom ψ φ)
    (fHom (ψ ≫ φ)).modulePullbackDerived
    ((iteratedToDerived X fHom ψ φ).totalLeftDerivedCounit
      (Hom.moduleLocalization (X l)) (Hom.ModuleQis (X l)))
    ((ToposHom.modulePullbackToDerived (fHom (ψ ≫ φ))).totalLeftDerivedCounit
      (Hom.moduleLocalization (X l)) (Hom.ModuleQis (X l)))
    (Hom.ModuleQis (X l))
    (compToDerivedIso X fHom ψ φ).symm

/-- Comparison from the composite of derived pullbacks to the iterated total left derived functor,
as the left-derived lift against the real iterated counit. -/
def compositeToIterated {l m n : SimplexCategory} (ψ : l ⟶ m) (φ : m ⟶ n) :
    (fHom ψ).modulePullbackDerived ⋙ (fHom φ).modulePullbackDerived ⟶
      iteratedDerived X fHom ψ φ :=
  (iteratedDerived X fHom ψ φ).leftDerivedLift
    ((iteratedToDerived X fHom ψ φ).totalLeftDerivedCounit
      (Hom.moduleLocalization (X l)) (Hom.ModuleQis (X l)))
    (Hom.ModuleQis (X l))
    ((fHom ψ).modulePullbackDerived ⋙ (fHom φ).modulePullbackDerived)
    (derivedPullbackCompCounit (fHom φ) (fHom ψ))

/-- The composite `Lf_ψ^* ⋙ Lf_φ^*` is a left-derived functor of the iterated homotopy-level
model. This competes with `iteratedDerived` and is not inferred from uniqueness of Kan
extensions. -/
instance isLeftDerivedFunctor_composite {l m n : SimplexCategory} (ψ : l ⟶ m) (φ : m ⟶ n) :
    ((fHom ψ).modulePullbackDerived ⋙
      (fHom φ).modulePullbackDerived).IsLeftDerivedFunctor
      (derivedPullbackCompCounit (fHom φ) (fHom ψ)) (Hom.ModuleQis (X l)) :=
  sorry

/-- Reverse comparison from the iterated total left derived functor to the composite of derived
pullbacks, as the left-derived lift against the real iterated counit. -/
def iteratedToComposite {l m n : SimplexCategory} (ψ : l ⟶ m) (φ : m ⟶ n) :
    iteratedDerived X fHom ψ φ ⟶
      (fHom ψ).modulePullbackDerived ⋙ (fHom φ).modulePullbackDerived :=
  ((fHom ψ).modulePullbackDerived ⋙ (fHom φ).modulePullbackDerived).leftDerivedLift
    (derivedPullbackCompCounit (fHom φ) (fHom ψ))
    (Hom.ModuleQis (X l))
    (iteratedDerived X fHom ψ φ)
    ((iteratedToDerived X fHom ψ φ).totalLeftDerivedCounit
      (Hom.moduleLocalization (X l)) (Hom.ModuleQis (X l)))

/-- Identification of the composite of derived pullbacks with the iterated total left derived
functor. Both legs are left-derived lifts against the real iterated counit. -/
def compositeIsoIterated {l m n : SimplexCategory} (ψ : l ⟶ m) (φ : m ⟶ n) :
    (fHom ψ).modulePullbackDerived ⋙ (fHom φ).modulePullbackDerived ≅
      iteratedDerived X fHom ψ φ where
  hom := compositeToIterated X fHom ψ φ
  inv := iteratedToComposite X fHom ψ φ
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- Canonical isomorphism `Lf_ψ^* ⋙ Lf_φ^* ≅ Lf_{ψ ≫ φ}^*` of derived module pullbacks.
The forward map is the existing `derivedPullbackCompComparisonOf`. The reverse is the real
`leftDerivedNatIso` inverse along `compToDerivedIso`, after identifying the composite of
derived pullbacks with the iterated total left derived functor by left-derived lifts. -/
def compComparisonIso {l m n : SimplexCategory} (ψ : l ⟶ m) (φ : m ⟶ n) :
    (fHom ψ).modulePullbackDerived ⋙ (fHom φ).modulePullbackDerived ≅
      (fHom (ψ ≫ φ)).modulePullbackDerived where
  hom := derivedPullbackCompComparisonOf (fHom φ) (fHom ψ) (fHom (ψ ≫ φ))
    (functoriality.pullbackCompIso ψ φ)
  inv := (compositeIsoIterated X fHom ψ φ ≪≫ iteratedDerivedIso X fHom ψ φ).inv
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The forward map of `compComparisonIso` is `derivedPullbackCompComparisonOf`. -/
theorem compComparisonIso_hom {l m n : SimplexCategory} (ψ : l ⟶ m) (φ : m ⟶ n) :
    (compComparisonIso X fHom ψ φ).hom =
      derivedPullbackCompComparisonOf (fHom φ) (fHom ψ) (fHom (ψ ≫ φ))
        (functoriality.pullbackCompIso ψ φ) :=
  sorry

/-- The pullback of `α` along a 2-face `δ i`, as a morphism in `D(O_2)`. -/
def facePullback (i : Fin 3)
    {K0 : Hom.ModuleDerived.{w} (X ⦋0⦌)}
    (α : (fHom (SimplexCategory.δ (1 : Fin 2))).modulePullbackDerived.obj K0 ≅
      (fHom (SimplexCategory.δ (0 : Fin 2))).modulePullbackDerived.obj K0) :
    (fHom (SimplexCategory.δ (1 : Fin 2) ≫ SimplexCategory.δ i)).modulePullbackDerived.obj K0 ⟶
      (fHom (SimplexCategory.δ (0 : Fin 2) ≫ SimplexCategory.δ i)).modulePullbackDerived.obj K0 :=
  (compComparisonIso X fHom (SimplexCategory.δ (1 : Fin 2)) (SimplexCategory.δ i)).inv.app K0 ≫
    (fHom (SimplexCategory.δ i)).modulePullbackDerived.map α.hom ≫
    (compComparisonIso X fHom (SimplexCategory.δ (0 : Fin 2)) (SimplexCategory.δ i)).hom.app K0

/-- `facePullback i α` is `Lf_{δ i}^* α` after the composition identifications. -/
theorem facePullback_eq (i : Fin 3)
    {K0 : Hom.ModuleDerived.{w} (X ⦋0⦌)}
    (α : (fHom (SimplexCategory.δ (1 : Fin 2))).modulePullbackDerived.obj K0 ≅
      (fHom (SimplexCategory.δ (0 : Fin 2))).modulePullbackDerived.obj K0) :
    facePullback X fHom i α =
      (compComparisonIso X fHom (SimplexCategory.δ (1 : Fin 2)) (SimplexCategory.δ i)).inv.app K0 ≫
        (fHom (SimplexCategory.δ i)).modulePullbackDerived.map α.hom ≫
        (compComparisonIso X fHom (SimplexCategory.δ (0 : Fin 2)) (SimplexCategory.δ i)).hom.app K0 :=
  sorry

/-- `(f_{δ 1})^{-1} α` transported to a morphism out of `Lf_{δ 1 ≫ δ 2}^* K_0`. -/
def cocycleLeft {K0 : Hom.ModuleDerived.{w} (X ⦋0⦌)}
    (α : (fHom (SimplexCategory.δ (1 : Fin 2))).modulePullbackDerived.obj K0 ≅
      (fHom (SimplexCategory.δ (0 : Fin 2))).modulePullbackDerived.obj K0) :
    (fHom (SimplexCategory.δ (1 : Fin 2) ≫ SimplexCategory.δ (2 : Fin 3))).modulePullbackDerived.obj
      K0 ⟶
      (fHom (SimplexCategory.δ (0 : Fin 2) ≫ SimplexCategory.δ (1 : Fin 3))).modulePullbackDerived.obj
        K0 :=
  (recodePullback X fHom (SimplexCategory.δ_comp_δ_self (i := (1 : Fin 2))).symm).hom.app K0 ≫
    facePullback X fHom 1 α

/-- `(f_{δ 0})^{-1} α ∘ (f_{δ 2})^{-1} α` after the `δ_comp_δ` identifications on `C_2`. -/
def cocycleRight {K0 : Hom.ModuleDerived.{w} (X ⦋0⦌)}
    (α : (fHom (SimplexCategory.δ (1 : Fin 2))).modulePullbackDerived.obj K0 ≅
      (fHom (SimplexCategory.δ (0 : Fin 2))).modulePullbackDerived.obj K0) :
    (fHom (SimplexCategory.δ (1 : Fin 2) ≫ SimplexCategory.δ (2 : Fin 3))).modulePullbackDerived.obj
      K0 ⟶
      (fHom (SimplexCategory.δ (0 : Fin 2) ≫ SimplexCategory.δ (1 : Fin 3))).modulePullbackDerived.obj
        K0 :=
  facePullback X fHom 2 α ≫
    (recodePullback X fHom
        (SimplexCategory.δ_comp_δ (i := (0 : Fin 2)) (j := (1 : Fin 2))
          (Fin.zero_le _))).hom.app K0 ≫
    facePullback X fHom 0 α ≫
    (recodePullback X fHom
        (SimplexCategory.δ_comp_δ (i := (0 : Fin 2)) (j := (0 : Fin 2))
          le_rfl).symm).hom.app K0

/-- `cocycleLeft` is `(f_{δ 1})^{-1} α` after recoding along `δ_comp_δ_self`. -/
theorem cocycleLeft_eq {K0 : Hom.ModuleDerived.{w} (X ⦋0⦌)}
    (α : (fHom (SimplexCategory.δ (1 : Fin 2))).modulePullbackDerived.obj K0 ≅
      (fHom (SimplexCategory.δ (0 : Fin 2))).modulePullbackDerived.obj K0) :
    cocycleLeft X fHom α =
      (recodePullback X fHom (SimplexCategory.δ_comp_δ_self (i := (1 : Fin 2))).symm).hom.app K0 ≫
        facePullback X fHom 1 α :=
  sorry

/-- `cocycleRight` is `(f_{δ 0})^{-1} α ∘ (f_{δ 2})^{-1} α` after the `δ_comp_δ`
identifications. -/
theorem cocycleRight_eq {K0 : Hom.ModuleDerived.{w} (X ⦋0⦌)}
    (α : (fHom (SimplexCategory.δ (1 : Fin 2))).modulePullbackDerived.obj K0 ≅
      (fHom (SimplexCategory.δ (0 : Fin 2))).modulePullbackDerived.obj K0) :
    cocycleRight X fHom α =
      facePullback X fHom 2 α ≫
        (recodePullback X fHom
            (SimplexCategory.δ_comp_δ (i := (0 : Fin 2)) (j := (1 : Fin 2))
              (Fin.zero_le _))).hom.app K0 ≫
        facePullback X fHom 0 α ≫
        (recodePullback X fHom
            (SimplexCategory.δ_comp_δ (i := (0 : Fin 2)) (j := (0 : Fin 2))
              le_rfl).symm).hom.app K0 :=
  sorry

/-- The stage object `K_n = Lf_{τ^n_n}^* K_0`. -/
def ofCocycleObj (K0 : Hom.ModuleDerived.{w} (X ⦋0⦌)) (n : SimplexCategory) :
    Hom.ModuleDerived.{w} (X n) :=
  (fHom (Sheaf.vertexOp n)).modulePullbackDerived.obj K0

/-- `ofCocycleObj K0 n` is the vertex pullback `Lf_{τ^n_n}^* K_0`. -/
theorem ofCocycleObj_eq (K0 : Hom.ModuleDerived.{w} (X ⦋0⦌)) (n : SimplexCategory) :
    ofCocycleObj X fHom K0 n = (fHom (Sheaf.vertexOp n)).modulePullbackDerived.obj K0 :=
  sorry

/-- The source comparison isomorphism `K_φ : Lf_φ^* K_m ≅ K_n`, obtained by recoding along
`τ^m_m ≫ φ = τ^n_{φ(m)n}` and applying `Lf_{τ^n_{φ(m)n}}^* α`. -/
def ofCocycleTransitionIso (K0 : Hom.ModuleDerived.{w} (X ⦋0⦌))
    (α : (fHom (SimplexCategory.δ (1 : Fin 2))).modulePullbackDerived.obj K0 ≅
      (fHom (SimplexCategory.δ (0 : Fin 2))).modulePullbackDerived.obj K0)
    {m n : SimplexCategory} (φ : m ⟶ n) :
    (fHom φ).modulePullbackDerived.obj (ofCocycleObj X fHom K0 m) ≅ ofCocycleObj X fHom K0 n :=
  (compComparisonIso X fHom (Sheaf.vertexOp m) φ).app K0 ≪≫
    (recodePullback X fHom
      (SimplexCategory.Hom.ext_zero_left (Sheaf.vertexOp m ≫ φ)
        (SimplexCategory.δ (1 : Fin 2) ≫ Sheaf.edgeOp φ))).app K0 ≪≫
    (compComparisonIso X fHom (SimplexCategory.δ (1 : Fin 2)) (Sheaf.edgeOp φ)).symm.app K0 ≪≫
    (fHom (Sheaf.edgeOp φ)).modulePullbackDerived.mapIso α ≪≫
    (compComparisonIso X fHom (SimplexCategory.δ (0 : Fin 2)) (Sheaf.edgeOp φ)).app K0 ≪≫
    (recodePullback X fHom
      (SimplexCategory.Hom.ext_zero_left
        (SimplexCategory.δ (0 : Fin 2) ≫ Sheaf.edgeOp φ)
        (Sheaf.vertexOp n))).app K0

/-- The forward map of `ofCocycleTransitionIso` is the source diagram for `K_φ`. -/
theorem ofCocycleTransitionIso_hom (K0 : Hom.ModuleDerived.{w} (X ⦋0⦌))
    (α : (fHom (SimplexCategory.δ (1 : Fin 2))).modulePullbackDerived.obj K0 ≅
      (fHom (SimplexCategory.δ (0 : Fin 2))).modulePullbackDerived.obj K0)
    {m n : SimplexCategory} (φ : m ⟶ n) :
    (ofCocycleTransitionIso X fHom K0 α φ).hom =
      ((compComparisonIso X fHom (Sheaf.vertexOp m) φ).app K0 ≪≫
        (recodePullback X fHom
          (SimplexCategory.Hom.ext_zero_left (Sheaf.vertexOp m ≫ φ)
            (SimplexCategory.δ (1 : Fin 2) ≫ Sheaf.edgeOp φ))).app K0 ≪≫
        (compComparisonIso X fHom (SimplexCategory.δ (1 : Fin 2)) (Sheaf.edgeOp φ)).symm.app K0 ≪≫
        (fHom (Sheaf.edgeOp φ)).modulePullbackDerived.mapIso α ≪≫
        (compComparisonIso X fHom (SimplexCategory.δ (0 : Fin 2)) (Sheaf.edgeOp φ)).app K0 ≪≫
        (recodePullback X fHom
          (SimplexCategory.Hom.ext_zero_left
            (SimplexCategory.δ (0 : Fin 2) ≫ Sheaf.edgeOp φ)
            (Sheaf.vertexOp n))).app K0).hom :=
  sorry

/-- The identity operator acts on the cocycle system by the canonical identity comparison. -/
theorem ofCocycle_map_id (K0 : Hom.ModuleDerived.{w} (X ⦋0⦌))
    (α : (fHom (SimplexCategory.δ (1 : Fin 2))).modulePullbackDerived.obj K0 ≅
      (fHom (SimplexCategory.δ (0 : Fin 2))).modulePullbackDerived.obj K0)
    (h : cocycleLeft X fHom α = cocycleRight X fHom α) (n : SimplexCategory) :
    (derivedPullbackIdComparisonOf (fHom (𝟙 n)) (functoriality.pullbackIdIso n)).app
        (ofCocycleObj X fHom K0 n) ≫
      (ofCocycleTransitionIso X fHom K0 α (𝟙 n)).hom =
      𝟙 (ofCocycleObj X fHom K0 n) :=
  sorry

/-- Transitions of the cocycle system respect composition of simplex operators after the
canonical comparison `Lf_φ^* ∘ Lf_ψ^* ⟶ Lf_{ψ ≫ φ}^*`. -/
theorem ofCocycle_map_comp (K0 : Hom.ModuleDerived.{w} (X ⦋0⦌))
    (α : (fHom (SimplexCategory.δ (1 : Fin 2))).modulePullbackDerived.obj K0 ≅
      (fHom (SimplexCategory.δ (0 : Fin 2))).modulePullbackDerived.obj K0)
    (h : cocycleLeft X fHom α = cocycleRight X fHom α)
    {l m n : SimplexCategory} (ψ : l ⟶ m) (φ : m ⟶ n) :
    (derivedPullbackCompComparisonOf (fHom φ) (fHom ψ) (fHom (ψ ≫ φ))
        (functoriality.pullbackCompIso ψ φ)).app (ofCocycleObj X fHom K0 l) ≫
      (ofCocycleTransitionIso X fHom K0 α (ψ ≫ φ)).hom =
      (fHom φ).modulePullbackDerived.map (ofCocycleTransitionIso X fHom K0 α ψ).hom ≫
        (ofCocycleTransitionIso X fHom K0 α φ).hom :=
  sorry

/-- The simplicial system `(K_n, K_φ)` of the derived category of modules assembled from
`K_0` in `D(O_0)` and an isomorphism `α : Lf_{δ 1}^* K_0 ≅ Lf_{δ 0}^* K_0` in
`D(O_1)` satisfying the `C_2` cocycle `cocycleLeft X fHom α = cocycleRight X fHom α`,
with `K_n = Lf_{τ^n_n}^* K_0`. -/
def ofCocycle (K0 : Hom.ModuleDerived.{w} (X ⦋0⦌))
    (α : (fHom (SimplexCategory.δ (1 : Fin 2))).modulePullbackDerived.obj K0 ≅
      (fHom (SimplexCategory.δ (0 : Fin 2))).modulePullbackDerived.obj K0)
    (h : cocycleLeft X fHom α = cocycleRight X fHom α) :
    DerivedModuleSystem X fHom :=
  of (ofCocycleObj X fHom K0) (fun φ ↦ (ofCocycleTransitionIso X fHom K0 α φ).hom)
    (ofCocycle_map_id X fHom K0 α h) (ofCocycle_map_comp X fHom K0 α h)

/-- The stage object of `ofCocycle` at `n` is `K_n = Lf_{τ^n_n}^* K_0`. -/
theorem ofCocycle_obj (K0 : Hom.ModuleDerived.{w} (X ⦋0⦌))
    (α : (fHom (SimplexCategory.δ (1 : Fin 2))).modulePullbackDerived.obj K0 ≅
      (fHom (SimplexCategory.δ (0 : Fin 2))).modulePullbackDerived.obj K0)
    (h : cocycleLeft X fHom α = cocycleRight X fHom α) (n : SimplexCategory) :
    (ofCocycle X fHom K0 α h).obj n = ofCocycleObj X fHom K0 n :=
  sorry

/-- The transition of `ofCocycle` at `φ` is the source comparison `K_φ`. -/
theorem ofCocycle_map (K0 : Hom.ModuleDerived.{w} (X ⦋0⦌))
    (α : (fHom (SimplexCategory.δ (1 : Fin 2))).modulePullbackDerived.obj K0 ≅
      (fHom (SimplexCategory.δ (0 : Fin 2))).modulePullbackDerived.obj K0)
    (h : cocycleLeft X fHom α = cocycleRight X fHom α) {m n : SimplexCategory} (φ : m ⟶ n) :
    (ofCocycle X fHom K0 α h).map φ = (ofCocycleTransitionIso X fHom K0 α φ).hom :=
  sorry

/-- The system constructed from `(K_0, α)` is cartesian: every `K_φ` is an isomorphism. -/
instance ofCocycle_isCartesian (K0 : Hom.ModuleDerived.{w} (X ⦋0⦌))
    (α : (fHom (SimplexCategory.δ (1 : Fin 2))).modulePullbackDerived.obj K0 ≅
      (fHom (SimplexCategory.δ (0 : Fin 2))).modulePullbackDerived.obj K0)
    (h : cocycleLeft X fHom α = cocycleRight X fHom α) :
    IsCartesian (ofCocycle X fHom K0 α h) where
  isIso_map := sorry

end General

section OnComponents

variable (C : SimplexCategory ⥤ Cat.{v, u}) (J : ∀ n, Precoverage (C.obj n))
variable [IsMorphismDiagram C J]
variable [∀ n, HasWeakSheafify (J n).toGrothendieck (Type w)]
variable [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (C.obj m)ᵒᵖ ⥤ Type w),
    ((C.map φ).toFunctor).op.HasLeftKanExtension P]
variable (O : Sheaf (topology C J) RingCat.{w})
variable [(topology C J).HasSheafCompose (forget RingCat.{w})]
variable [∀ n, ((J n).toGrothendieck).HasSheafCompose (forget RingCat.{w})]
variable [UnivLE.{max u v, w}]
variable [∀ {m n : SimplexCategory} (φ : m ⟶ n),
    (SheafOfModules.restrictScalars.{w}
      (ringedToposMap C J O φ).structureMap).IsRightAdjoint]
variable [∀ {m n : SimplexCategory} (φ : m ⟶ n),
    ToposHom.HasModulePullbackDerived (ringedToposMap C J O φ)]

/-- Case A of Situation 85.3.3: the cartesian derived-module system on component ringed sites
assembled from `K_0` and a coface cocycle, using `ringedToposMap`. -/
def ofCocycleOnComponents
    (K0 : Hom.ModuleDerived.{w} (componentRingedSite C J O ⦋0⦌))
    (α : (ringedToposMap C J O (SimplexCategory.δ (1 : Fin 2))).modulePullbackDerived.obj K0 ≅
      (ringedToposMap C J O (SimplexCategory.δ (0 : Fin 2))).modulePullbackDerived.obj K0)
    (h : cocycleLeft (fun n ↦ componentRingedSite C J O n)
        (fun φ ↦ ringedToposMap C J O φ) α =
      cocycleRight (fun n ↦ componentRingedSite C J O n)
        (fun φ ↦ ringedToposMap C J O φ) α) :
    DerivedModuleSystemOnComponents C J O :=
  ofCocycle (fun n ↦ componentRingedSite C J O n)
    (fun φ ↦ ringedToposMap C J O φ) K0 α h

/-- `ofCocycleOnComponents` is `ofCocycle` for `ringedToposMap` on component ringed sites. -/
theorem ofCocycleOnComponents_eq
    (K0 : Hom.ModuleDerived.{w} (componentRingedSite C J O ⦋0⦌))
    (α : (ringedToposMap C J O (SimplexCategory.δ (1 : Fin 2))).modulePullbackDerived.obj K0 ≅
      (ringedToposMap C J O (SimplexCategory.δ (0 : Fin 2))).modulePullbackDerived.obj K0)
    (h : cocycleLeft (fun n ↦ componentRingedSite C J O n)
        (fun φ ↦ ringedToposMap C J O φ) α =
      cocycleRight (fun n ↦ componentRingedSite C J O n)
        (fun φ ↦ ringedToposMap C J O φ) α) :
    ofCocycleOnComponents C J O K0 α h =
      ofCocycle (fun n ↦ componentRingedSite C J O n)
        (fun φ ↦ ringedToposMap C J O φ) K0 α h :=
  sorry

/-- The case A specialization of `ofCocycle` is cartesian. -/
instance ofCocycleOnComponents_isCartesian
    (K0 : Hom.ModuleDerived.{w} (componentRingedSite C J O ⦋0⦌))
    (α : (ringedToposMap C J O (SimplexCategory.δ (1 : Fin 2))).modulePullbackDerived.obj K0 ≅
      (ringedToposMap C J O (SimplexCategory.δ (0 : Fin 2))).modulePullbackDerived.obj K0)
    (h : cocycleLeft (fun n ↦ componentRingedSite C J O n)
        (fun φ ↦ ringedToposMap C J O φ) α =
      cocycleRight (fun n ↦ componentRingedSite C J O n)
        (fun φ ↦ ringedToposMap C J O φ) α) :
    IsCartesian (ofCocycleOnComponents C J O K0 α h) :=
  ofCocycle_isCartesian (fun n ↦ componentRingedSite C J O n)
    (fun φ ↦ ringedToposMap C J O φ) K0 α h

end OnComponents

end CategoryTheory.SimplicialSites.DerivedModuleSystem
