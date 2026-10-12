/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.Ring.Sheaf.Units

/-!
# Maps of additive units sheaves

This file constructs the morphism on additive units sheaves induced by a
morphism of commutative-ring sheaves.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u v

namespace CategoryTheory.Sheaf

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {A Q R : Sheaf J CommRingCat.{max u v}}
variable [J.HasSheafCompose (CategoryTheory.forget CommRingCat.{max u v})]

/-- The additive-units section represented by a bundled unit. This is the
choice-based inverse to the public section readout; its specifications below
make downstream uses independent of the chosen inverse. -/
noncomputable def unitsAddSheafSection (A : Sheaf J CommRingCat.{max u v})
    {U : Cᵒᵖ} (g : (A.1.obj U)ˣ) : (unitsAddSheaf A).1.obj U :=
  Function.invFun (unitsAddSheafValue A) g.1

/-- Reading out `unitsAddSheafSection A g` recovers the underlying ring
section of `g`. -/
theorem unitsAddSheafValue_section (A : Sheaf J CommRingCat.{max u v})
    {U : Cᵒᵖ} (g : (A.1.obj U)ˣ) :
    unitsAddSheafValue A (unitsAddSheafSection A g) = g.1 := sorry

/-- A section of the additive units sheaf, regarded as its bundled unit. -/
noncomputable def unitsAddSheafUnit (A : Sheaf J CommRingCat.{max u v})
    {U : Cᵒᵖ} (g : (unitsAddSheaf A).1.obj U) : (A.1.obj U)ˣ :=
  Function.invFun (unitsAddSheafSection A) g

/-- Converting an additive-units section to a unit and back recovers the
section. -/
theorem unitsAddSheafSection_unit (A : Sheaf J CommRingCat.{max u v})
    {U : Cᵒᵖ} (g : (unitsAddSheaf A).1.obj U) :
    unitsAddSheafSection A (unitsAddSheafUnit A g) = g := sorry

/-- The sectionwise function on additive units induced by a morphism of
commutative-ring sheaves. -/
noncomputable def unitsAddMapFunction (π : A ⟶ Q) (U : Cᵒᵖ) :
    (unitsAddSheaf A).1.obj U → (unitsAddSheaf Q).1.obj U :=
  fun g ↦ unitsAddSheafSection Q
    (Units.map (π.hom.app U).hom.toMonoidHom (unitsAddSheafUnit A g))

/-- The induced function on additive units preserves zero. -/
theorem unitsAddMapFunction_zero (π : A ⟶ Q) (U : Cᵒᵖ) :
    unitsAddMapFunction π U 0 = 0 := sorry

/-- The induced function on additive units preserves addition. -/
theorem unitsAddMapFunction_add (π : A ⟶ Q) (U : Cᵒᵖ)
    (x y : (unitsAddSheaf A).1.obj U) :
    unitsAddMapFunction π U (x + y) =
      unitsAddMapFunction π U x + unitsAddMapFunction π U y := sorry

/-- The additive homomorphism on units sections induced by a morphism of
commutative-ring sheaves. -/
noncomputable def unitsAddMapHom (π : A ⟶ Q) (U : Cᵒᵖ) :
    (unitsAddSheaf A).1.obj U →+ (unitsAddSheaf Q).1.obj U where
  toFun := unitsAddMapFunction π U
  map_zero' := unitsAddMapFunction_zero π U
  map_add' := unitsAddMapFunction_add π U

/-- Naturality of the sectionwise map on additive units induced by a morphism of
commutative-ring sheaves. -/
theorem unitsAddMap_naturality (π : A ⟶ Q) {U V : Cᵒᵖ} (i : U ⟶ V) :
    (unitsAddSheaf A).1.map i ≫
        AddCommGrpCat.ofHom (unitsAddMapHom π V) =
      AddCommGrpCat.ofHom (unitsAddMapHom π U) ≫
        (unitsAddSheaf Q).1.map i := sorry

/-- The morphism of additive units sheaves induced by a morphism of
commutative-ring sheaves. -/
noncomputable def unitsAddMap (π : A ⟶ Q) :
    unitsAddSheaf A ⟶ unitsAddSheaf Q :=
  ObjectProperty.homMk
    { app := fun U ↦ AddCommGrpCat.ofHom (unitsAddMapHom π U)
      naturality := fun {_ _} i ↦ unitsAddMap_naturality π i }

/-- The component of `unitsAddMap π` is the additive form of the usual map on
units. -/
theorem unitsAddMap_app (π : A ⟶ Q) (U : Cᵒᵖ) :
    (unitsAddMap π).hom.app U =
      AddCommGrpCat.ofHom (unitsAddMapHom π U) := sorry

/-- The map on additive units sheaves induced by an identity is the identity. -/
theorem unitsAddMap_id (A : Sheaf J CommRingCat.{max u v}) :
    unitsAddMap (𝟙 A) = 𝟙 (unitsAddSheaf A) := sorry

/-- Maps on additive units sheaves respect composition. -/
theorem unitsAddMap_comp (π : A ⟶ Q) (ρ : Q ⟶ R) :
    unitsAddMap (π ≫ ρ) = unitsAddMap π ≫ unitsAddMap ρ := sorry

end CategoryTheory.Sheaf
