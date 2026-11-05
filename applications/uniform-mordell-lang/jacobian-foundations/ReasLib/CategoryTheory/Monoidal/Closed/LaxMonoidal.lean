module

public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Lax monoidal functors and internal Hom

A lax monoidal functor carries a canonical comparison from the image of an internal Hom to the
internal Hom of the images whenever the source object and its image are closed.  This file owns
that construction at its natural objectwise level, independently of sheaves or geometry.
-/

@[expose] public section

open CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed

noncomputable section

universe u₁ v₁ u₂ v₂

namespace CategoryTheory.Functor.LaxMonoidal.InternalHom

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable [MonoidalCategory C] [MonoidalCategory D]
variable (F : C ⥤ D) [F.LaxMonoidal]

/-- The evaluation map whose curry is the internal-Hom comparison of a lax monoidal functor. -/
@[stacks 0GMX "generic evaluation"]
noncomputable def evaluation (X Y : C) [Closed X] :
    F.obj X ⊗ F.obj ((ihom X).obj Y) ⟶ F.obj Y :=
  μ F X ((ihom X).obj Y) ≫ F.map ((ihom.ev X).app Y)

/-- A lax monoidal functor maps an internal Hom to the internal Hom of the images. -/
@[stacks 0GMX "generic comparison"]
noncomputable def comparison (X Y : C) [Closed X] [Closed (F.obj X)] :
    F.obj ((ihom X).obj Y) ⟶ (ihom (F.obj X)).obj (F.obj Y) :=
  curry (evaluation F X Y)

/-- Uncurrying the internal-Hom comparison recovers its defining evaluation map. -/
@[simp]
theorem uncurry_comparison (X Y : C) [Closed X] [Closed (F.obj X)] :
    uncurry (comparison F X Y) = evaluation F X Y :=
  uncurry_curry _

/-- Evaluation after the internal-Hom comparison is the defining uncurried map. -/
@[simp]
theorem comparison_ev (X Y : C) [Closed X] [Closed (F.obj X)] :
    F.obj X ◁ comparison F X Y ≫
        (ihom.ev (F.obj X)).app (F.obj Y) =
      evaluation F X Y := by
  rw [← uncurry_eq, uncurry_comparison]

set_option backward.isDefEq.respectTransparency false in
/-- The lax-monoidal internal-Hom comparison is natural in its target variable. -/
theorem naturality (X : C) [Closed X] [Closed (F.obj X)]
    {Y Z : C} (g : Y ⟶ Z) :
    F.map ((ihom X).map g) ≫ comparison F X Z =
      comparison F X Y ≫ (ihom (F.obj X)).map (F.map g) := by
  apply uncurry_injective
  rw [uncurry_natural_left, uncurry_natural_right,
    uncurry_comparison, uncurry_comparison]
  dsimp only [evaluation]
  rw [Functor.LaxMonoidal.μ_natural_right_assoc, ← F.map_comp,
    ihom.ev_naturality, F.map_comp]
  simp only [Category.assoc]

set_option backward.isDefEq.respectTransparency false in
/-- The lax-monoidal internal-Hom comparison is contravariantly natural in its source variable. -/
theorem naturality_left {W X : C}
    [Closed W] [Closed X] [Closed (F.obj W)] [Closed (F.obj X)]
    (g : W ⟶ X) (Y : C) :
    comparison F X Y ≫ (pre (F.map g)).app (F.obj Y) =
      F.map ((pre g).app Y) ≫ comparison F W Y := by
  apply uncurry_injective
  rw [uncurry_pre_app, uncurry_natural_left,
    uncurry_comparison, uncurry_comparison]
  dsimp only [evaluation]
  rw [Functor.LaxMonoidal.μ_natural_left_assoc,
    Functor.LaxMonoidal.μ_natural_right_assoc, ← F.map_comp, ← F.map_comp,
    id_tensor_pre_app_comp_ev]

/-- For a fixed source object, the internal-Hom comparisons of a lax monoidal functor form a
natural transformation. -/
@[stacks 0GMX "generic natural comparison"]
noncomputable def natTrans (X : C) [Closed X] [Closed (F.obj X)] :
    ihom X ⋙ F ⟶ F ⋙ ihom (F.obj X) where
  app Y := comparison F X Y
  naturality _ _ g := naturality F X g

/-- The component of `natTrans` is the canonical internal-Hom comparison. -/
@[simp]
theorem natTrans_app (X Y : C) [Closed X] [Closed (F.obj X)] :
    (natTrans F X).app Y = comparison F X Y := rfl

end CategoryTheory.Functor.LaxMonoidal.InternalHom

namespace CategoryTheory.Functor.LaxMonoidal

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable [MonoidalCategory C] [MonoidalCategory D]
variable (F : C ⥤ D) [F.LaxMonoidal]

/-- A lax monoidal functor preserves internal Homs when its canonical comparison is invertible
for every source object which is closed and whose image is closed. -/
@[stacks 0GMX "preservation property"]
class PreservesInternalHom : Prop where
  isIso_comparison (X Y : C) [Closed X] [Closed (F.obj X)] :
    IsIso (InternalHom.comparison F X Y)

/-- A preservation hypothesis supplies invertibility of each internal-Hom comparison to
typeclass search. -/
instance [PreservesInternalHom F] (X Y : C) [Closed X] [Closed (F.obj X)] :
    IsIso (InternalHom.comparison F X Y) :=
  PreservesInternalHom.isIso_comparison X Y

namespace InternalHom

/-- The unique named inverse owner for an invertible lax-monoidal internal-Hom comparison.

This component-level API only needs the categorical gate `[IsIso (comparison F X Y)]`; a
`PreservesInternalHom F` hypothesis supplies that gate through the instance above. -/
@[stacks 0GMX "generic comparison inverse"]
noncomputable def comparisonInv (X Y : C) [Closed X] [Closed (F.obj X)]
    [IsIso (comparison F X Y)] :
    (ihom (F.obj X)).obj (F.obj Y) ⟶ F.obj ((ihom X).obj Y) :=
  CategoryTheory.inv (comparison F X Y)

/-- The comparison followed by its named inverse is the identity. -/
@[stacks 0GMX "generic comparison inverse law"]
theorem comparison_comp_comparisonInv (X Y : C) [Closed X] [Closed (F.obj X)]
    [IsIso (comparison F X Y)] :
    comparison F X Y ≫ comparisonInv F X Y = 𝟙 _ :=
  IsIso.hom_inv_id _

/-- The named inverse followed by the comparison is the identity. -/
@[stacks 0GMX "generic comparison inverse law"]
theorem comparisonInv_comp_comparison (X Y : C) [Closed X] [Closed (F.obj X)]
    [IsIso (comparison F X Y)] :
    comparisonInv F X Y ≫ comparison F X Y = 𝟙 _ :=
  IsIso.inv_hom_id _

/-- The canonical internal-Hom comparison bundled with its named inverse. -/
@[stacks 0GMX "generic comparison isomorphism"]
noncomputable def comparisonIso (X Y : C) [Closed X] [Closed (F.obj X)]
    [IsIso (comparison F X Y)] :
    F.obj ((ihom X).obj Y) ≅ (ihom (F.obj X)).obj (F.obj Y) :=
  { hom := comparison F X Y
    inv := comparisonInv F X Y
    hom_inv_id := comparison_comp_comparisonInv F X Y
    inv_hom_id := comparisonInv_comp_comparison F X Y }

/-- The forward projection of the canonical comparison isomorphism. -/
@[stacks 0GMX "generic comparison isomorphism hom", simp]
theorem comparisonIso_hom (X Y : C) [Closed X] [Closed (F.obj X)]
    [IsIso (comparison F X Y)] :
    (comparisonIso F X Y).hom = comparison F X Y := rfl

/-- The inverse projection of the canonical comparison isomorphism. -/
@[stacks 0GMX "generic comparison isomorphism inv", simp]
theorem comparisonIso_inv (X Y : C) [Closed X] [Closed (F.obj X)]
    [IsIso (comparison F X Y)] :
    (comparisonIso F X Y).inv = comparisonInv F X Y := rfl

/-- Naturality of the named inverse comparison for a fixed source object. -/
@[stacks 0GMX "generic inverse comparison naturality"]
theorem comparisonInv_naturality [PreservesInternalHom F]
    (X : C) [Closed X] [Closed (F.obj X)] {Y Z : C} (g : Y ⟶ Z) :
    (ihom (F.obj X)).map (F.map g) ≫ comparisonInv F X Z =
      comparisonInv F X Y ≫ F.map ((ihom X).map g) := by
  -- Local instance justification (proof-local temporary data): invert the source component for inverse naturality.
  letI : IsIso ((natTrans F X).app Y) :=
    PreservesInternalHom.isIso_comparison X Y
  -- Local instance justification (proof-local temporary data): invert the target component for inverse naturality.
  letI : IsIso ((natTrans F X).app Z) :=
    PreservesInternalHom.isIso_comparison X Z
  change (F ⋙ ihom (F.obj X)).map g ≫
      CategoryTheory.inv ((natTrans F X).app Z) =
    CategoryTheory.inv ((natTrans F X).app Y) ≫ (ihom X ⋙ F).map g
  exact ((natTrans F X).naturality_inv g).symm

/-- The fixed-source inverse natural transformation, with the component inverse as its owner. -/
@[stacks 0GMX "generic inverse natural comparison"]
noncomputable def natTransInv [PreservesInternalHom F]
    (X : C) [Closed X] [Closed (F.obj X)] :
    F ⋙ ihom (F.obj X) ⟶ ihom X ⋙ F where
  app Y := comparisonInv F X Y
  naturality _ _ g := comparisonInv_naturality F X g

/-- A component of the fixed-source inverse natural transformation is the named comparison
inverse. -/
@[stacks 0GMX "generic inverse natural comparison app", simp]
theorem natTransInv_app [PreservesInternalHom F]
    (X Y : C) [Closed X] [Closed (F.obj X)] :
    (natTransInv F X).app Y = comparisonInv F X Y := rfl

/-- The forward and inverse natural comparisons compose to the identity natural transformation. -/
@[stacks 0GMX "generic natural comparison inverse law"]
theorem natTrans_comp_natTransInv [PreservesInternalHom F]
    (X : C) [Closed X] [Closed (F.obj X)] :
    natTrans F X ≫ natTransInv F X = 𝟙 _ := by
  ext Y
  exact comparison_comp_comparisonInv F X Y

/-- The inverse and forward natural comparisons compose to the identity natural transformation. -/
@[stacks 0GMX "generic natural comparison inverse law"]
theorem natTransInv_comp_natTrans [PreservesInternalHom F]
    (X : C) [Closed X] [Closed (F.obj X)] :
    natTransInv F X ≫ natTrans F X = 𝟙 _ := by
  ext Y
  exact comparisonInv_comp_comparison F X Y

/-- The forward and inverse comparison components compose to the identity. -/
@[stacks 0GMX "generic natural comparison component law"]
theorem natTrans_app_comp_natTransInv_app [PreservesInternalHom F]
    (X Y : C) [Closed X] [Closed (F.obj X)] :
    (natTrans F X).app Y ≫ (natTransInv F X).app Y = 𝟙 _ :=
  comparison_comp_comparisonInv F X Y

/-- The inverse and forward comparison components compose to the identity. -/
@[stacks 0GMX "generic natural comparison component law"]
theorem natTransInv_app_comp_natTrans_app [PreservesInternalHom F]
    (X Y : C) [Closed X] [Closed (F.obj X)] :
    (natTransInv F X).app Y ≫ (natTrans F X).app Y = 𝟙 _ :=
  comparisonInv_comp_comparison F X Y

/-- For a functor preserving internal Homs, the comparisons with a fixed source object assemble
into a natural isomorphism. -/
@[stacks 0GMX "generic comparison natural isomorphism"]
noncomputable def natIso [PreservesInternalHom F]
    (X : C) [Closed X] [Closed (F.obj X)] :
    ihom X ⋙ F ≅ F ⋙ ihom (F.obj X) :=
  { hom := natTrans F X
    inv := natTransInv F X
    hom_inv_id := natTrans_comp_natTransInv F X
    inv_hom_id := natTransInv_comp_natTrans F X }

/-- The forward natural-transformation projection of `natIso`. -/
@[stacks 0GMX "generic natural comparison hom", simp]
theorem natIso_hom [PreservesInternalHom F]
    (X : C) [Closed X] [Closed (F.obj X)] :
    (natIso F X).hom = natTrans F X := rfl

/-- The inverse natural-transformation projection of `natIso`. -/
@[stacks 0GMX "generic natural comparison inv", simp]
theorem natIso_inv [PreservesInternalHom F]
    (X : C) [Closed X] [Closed (F.obj X)] :
    (natIso F X).inv = natTransInv F X := rfl

/-- The forward component of the internal-Hom comparison natural isomorphism is the canonical
comparison morphism. -/
@[stacks 0GMX "generic natural comparison hom app", simp]
theorem natIso_hom_app [PreservesInternalHom F]
    (X Y : C) [Closed X] [Closed (F.obj X)] :
    (natIso F X).hom.app Y = comparison F X Y := rfl

/-- The inverse component of the internal-Hom comparison natural isomorphism is the named
component inverse. -/
@[stacks 0GMX "generic natural comparison inv app", simp]
theorem natIso_inv_app [PreservesInternalHom F]
    (X Y : C) [Closed X] [Closed (F.obj X)] :
    (natIso F X).inv.app Y = comparisonInv F X Y := rfl


-- The inverse natural transformation and both natural inverse laws are named explicitly above;
-- the only deferred content in this bundle is Prop-valued categorical law data.

end InternalHom

end CategoryTheory.Functor.LaxMonoidal
