/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Action.ModuleCat.OpenStabilizer.Submodule

/-!
# Coreflection to actions with open stabilizers

The invariant submodule of open-stabilizer elements is functorial and is right adjoint to the
inclusion of discrete continuous module actions into all algebraic module actions.
-/

@[expose] public section

open CategoryTheory Limits
open scoped Topology

universe u v

namespace CategoryTheory.Action.ModuleCat.OpenStabilizer

noncomputable section

variable (R : Type u) [Ring R]
variable (G : Type v) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- The restricted action consists entirely of elements with open stabilizer. -/
theorem action_mem (X : Action (ModuleCat.{max u v} R) G) :
    openStabilizer R G (action R G X) := sorry

/-- The open-stabilizer coreflection object of an algebraic linear action. -/
def obj (X : Action (ModuleCat.{max u v} R) G) : DiscreteModuleCat R G where
  obj := action R G X
  property := action_mem R G X

/-- The open-stabilizer coreflection on morphisms. -/
def hom {X Y : Action (ModuleCat.{max u v} R) G} (f : X ⟶ Y) :
    obj R G X ⟶ obj R G Y :=
  ObjectProperty.homMk (actionMap R G f)

/-- The open-stabilizer restriction of an identity morphism is an identity. -/
theorem hom_id (X : Action (ModuleCat.{max u v} R) G) :
    hom R G (𝟙 X) = 𝟙 (obj R G X) := sorry

/-- Open-stabilizer restriction preserves composition. -/
theorem hom_comp {X Y Z : Action (ModuleCat.{max u v} R) G}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    hom R G (f ≫ g) = hom R G f ≫ hom R G g := sorry

/-- The functor coreflecting an algebraic action to its open-stabilizer subaction. -/
@[stacks 04JF "open-stabilizer coreflector"]
def coreflector :
    Action (ModuleCat.{max u v} R) G ⥤ DiscreteModuleCat R G where
  obj := obj R G
  map := hom R G
  map_id := hom_id R G
  map_comp := hom_comp R G

/-- The open-stabilizer submodule inclusion commutes with the group action. -/
theorem subtype_naturality (Y : Action (ModuleCat.{max u v} R) G) (g : G) :
    (action R G Y).ρ g ≫ ModuleCat.ofHom (submodule R G Y).subtype =
      ModuleCat.ofHom (submodule R G Y).subtype ≫ Y.ρ g := sorry

/-- The canonical inclusion of the open-stabilizer subaction into its ambient action. -/
def subtypeHom (Y : Action (ModuleCat.{max u v} R) G) : (obj R G Y).obj ⟶ Y where
  hom := ModuleCat.ofHom (submodule R G Y).subtype
  comm := subtype_naturality R G Y

/-- The underlying linear map of the universal factor through the open-stabilizer subaction. -/
def factorLinearMap {X : DiscreteModuleCat R G}
    {Y : Action (ModuleCat.{max u v} R) G}
    (f : (openStabilizer R G).ι.obj X ⟶ Y) :
    X.obj.V →ₗ[R] submodule R G Y :=
  LinearMap.codRestrict (submodule R G Y) f.hom.hom
    fun x ↦ isOpen_stabilizer_map R G f (X.property x)

/-- The universal factor's underlying map is equivariant. -/
theorem factorLinearMap_naturality {X : DiscreteModuleCat R G}
    {Y : Action (ModuleCat.{max u v} R) G}
    (f : (openStabilizer R G).ι.obj X ⟶ Y) (g : G) :
    X.obj.ρ g ≫ ModuleCat.ofHom (factorLinearMap R G f) =
      ModuleCat.ofHom (factorLinearMap R G f) ≫ (action R G Y).ρ g := sorry

/-- Every map from an open-stabilizer action factors through the target's open-stabilizer
subaction. -/
def factor {X : DiscreteModuleCat R G} {Y : Action (ModuleCat.{max u v} R) G}
    (f : (openStabilizer R G).ι.obj X ⟶ Y) : X ⟶ obj R G Y :=
  ObjectProperty.homMk
    { hom := ModuleCat.ofHom (factorLinearMap R G f)
      comm := factorLinearMap_naturality R G f }

/-- Composing the universal factor with the subaction inclusion recovers the original map. -/
theorem factor_comp_subtypeHom {X : DiscreteModuleCat R G}
    {Y : Action (ModuleCat.{max u v} R) G}
    (f : (openStabilizer R G).ι.obj X ⟶ Y) :
    (factor R G f).hom ≫ subtypeHom R G Y = f := sorry

/-- Factoring a map already landing in the coreflection recovers that map. -/
theorem factor_subtypeHom_comp {X : DiscreteModuleCat R G}
    {Y : Action (ModuleCat.{max u v} R) G} (f : X ⟶ obj R G Y) :
    factor R G (f.hom ≫ subtypeHom R G Y) = f := sorry

/-- The universal Hom equivalence of the open-stabilizer coreflection. -/
def homEquiv (X : DiscreteModuleCat R G)
    (Y : Action (ModuleCat.{max u v} R) G) :
    ((openStabilizer R G).ι.obj X ⟶ Y) ≃ (X ⟶ (coreflector R G).obj Y) where
  toFun := factor R G
  invFun := fun f ↦ f.hom ≫ subtypeHom R G Y
  left_inv := factor_comp_subtypeHom R G
  right_inv := factor_subtypeHom_comp R G

/-- The coreflection Hom equivalence is natural in the discrete source. -/
theorem homEquiv_naturality_left_symm
    {X' X : DiscreteModuleCat R G} {Y : Action (ModuleCat.{max u v} R) G}
    (f : X' ⟶ X) (g : X ⟶ (coreflector R G).obj Y) :
    (homEquiv R G X' Y).symm (f ≫ g) =
      (openStabilizer R G).ι.map f ≫ (homEquiv R G X Y).symm g := sorry

/-- The coreflection Hom equivalence is natural in the ambient target. -/
theorem homEquiv_naturality_right
    {X : DiscreteModuleCat R G}
    {Y Y' : Action (ModuleCat.{max u v} R) G}
    (f : (openStabilizer R G).ι.obj X ⟶ Y) (g : Y ⟶ Y') :
    homEquiv R G X Y' (f ≫ g) =
      homEquiv R G X Y f ≫ (coreflector R G).map g := sorry

/-- The inclusion of open-stabilizer actions is left adjoint to the open-stabilizer
coreflector. -/
@[stacks 04JF "open-stabilizer coreflection adjunction"]
noncomputable def adjunction : (openStabilizer R G).ι ⊣ coreflector R G :=
  Adjunction.mkOfHomEquiv
    { homEquiv := homEquiv R G
      homEquiv_naturality_left_symm := homEquiv_naturality_left_symm R G
      homEquiv_naturality_right := homEquiv_naturality_right R G }

/-- The coreflection inclusion is the submodule inclusion on underlying elements. -/
@[simp]
theorem subtypeHom_apply (Y : Action (ModuleCat.{max u v} R) G)
    (y : (obj R G Y).obj.V) : (subtypeHom R G Y).hom.hom y = y.1 := sorry

/-- The universal factor sends an element to the same underlying element in the target. -/
@[simp]
theorem factor_apply {X : DiscreteModuleCat R G}
    {Y : Action (ModuleCat.{max u v} R) G}
    (f : (openStabilizer R G).ι.obj X ⟶ Y) (x : X.obj.V) :
    ((factor R G f).hom.hom x).1 = f.hom.hom x := sorry

/-- The full-subcategory inclusion detects zero objects. -/
theorem isZero_of_inclusion_obj_isZero (X : DiscreteModuleCat R G)
    (hX : IsZero ((openStabilizer R G).ι.obj X)) : IsZero X := sorry

end

end CategoryTheory.Action.ModuleCat.OpenStabilizer
