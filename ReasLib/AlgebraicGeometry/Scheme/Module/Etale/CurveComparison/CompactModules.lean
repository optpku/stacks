module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.CompactCharacters
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
public import Mathlib.CategoryTheory.Action.Basic
public import Mathlib.CategoryTheory.Abelian.Transfer

@[expose] public section

open CategoryTheory

noncomputable section

universe u

/-- Actual compact Hausdorff modules, with continuous linear maps as morphisms.
For finite coefficients these are profinite; disconnectedness is not assumed
as a stronger replacement for the source's compact category. -/
structure CompactModule (Λ : Type u) [CommRing Λ] where
  toModule : ModuleCat.{u} Λ
  [topology : TopologicalSpace toModule]
  [compact : CompactSpace toModule]
  [t2 : T2Space toModule]
  [topologicalAdd : IsTopologicalAddGroup toModule]
  [scalarContinuous : ContinuousConstSMul Λ toModule]

attribute [instance] CompactModule.topology CompactModule.compact CompactModule.t2
  CompactModule.topologicalAdd CompactModule.scalarContinuous

namespace CompactModule

variable (Λ : Type u) [CommRing Λ]

instance : Category (CompactModule Λ) where
  Hom M N := M.toModule →L[Λ] N.toModule
  id M := ContinuousLinearMap.id Λ M.toModule
  comp f g := g.comp f
  id_comp := by intros; rfl
  comp_id := by intros; rfl
  assoc := by intros; rfl

instance : Preadditive (CompactModule Λ) where
  homGroup M N := inferInstanceAs (AddCommGroup (M.toModule →L[Λ] N.toModule))
  add_comp P Q R f f' g := by
    apply ContinuousLinearMap.ext
    intro x
    exact (show Q.toModule →L[Λ] R.toModule from g).map_add _ _
  comp_add := by intros; rfl

/-- The underlying linear map, without changing scalar action. -/
def linear {M N : CompactModule Λ} (f : M ⟶ N) : M.toModule →ₗ[Λ] N.toModule :=
  (show M.toModule →L[Λ] N.toModule from f).toLinearMap

/-- Forget only the compact topology. -/
def forget : CompactModule Λ ⥤ ModuleCat.{u} Λ where
  obj M := M.toModule
  map f := ModuleCat.ofHom (linear Λ f)
  map_id _ := rfl
  map_comp _ _ := rfl

instance : (forget Λ).Additive where
  map_add := by intros; rfl

/-- Compact topology on the actual character group of a discrete module. -/
def ofCharacter [Finite Λ] (M : ModuleCat.{u} Λ) : CompactModule Λ where
  toModule := ModuleCat.of Λ (CompactCharacters.Dual Λ M)

/-- Character precomposition is continuous for the finite-coordinate topology. -/
def dualMap [Finite Λ] {M N : ModuleCat.{u} Λ} (f : M ⟶ N) :
    ofCharacter Λ N ⟶ ofCharacter Λ M :=
  { toLinearMap := CharacterModule.dual f.hom
    cont := CompactCharacters.continuous_map Λ M f.hom }

/-- Character duality into actual compact modules. -/
def characterFunctor [Finite Λ] : (ModuleCat.{u} Λ)ᵒᵖ ⥤ CompactModule Λ where
  obj M := ofCharacter Λ M.unop
  map f := dualMap Λ f.unop
  map_id := by intros; apply ContinuousLinearMap.ext; intro χ; apply CharacterModule.ext; intro m; rfl
  map_comp := by intros; apply ContinuousLinearMap.ext; intro χ; apply CharacterModule.ext; intro m; rfl

end CompactModule

namespace CompactRepresentation

variable (Λ G : Type u) [CommRing Λ] [Group G] [TopologicalSpace G]

/-- Joint continuity of the actual linear action on a compact module. -/
def continuousAction : ObjectProperty (Action (CompactModule Λ) G) :=
  fun M ↦ Continuous (fun gm : G × M.V.toModule ↦
    CompactModule.linear Λ (M.ρ gm.1) gm.2)

/-- The category of compact modules with continuous G-action. -/
abbrev Cat := (continuousAction Λ G).FullSubcategory

end CompactRepresentation
