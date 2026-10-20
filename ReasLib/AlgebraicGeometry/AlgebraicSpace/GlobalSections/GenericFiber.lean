/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.GlobalSections
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FieldFiber
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ResidueField

/-!
# Global sections of residue-field fibres

The structure morphism of a residue-field fibre induces a canonical map from the
residue field to its ring of global sections, constructed using an atlas equalizer.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Hom

/-- The morphism of schemes over `S` from the chosen atlas of the field-valued
fibre `X_ξ` to `Spec κ(ξ)`. -/
noncomputable def genericFiberAtlasOverHom {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    [IsDecent Y] (f : X ⟶ Y) (ξ : Points Y) :
    (chosenPresentation (fieldFiber f (FieldValuedPoint.residuePoint ξ))).U ⟶
      (FieldValuedPoint.residuePoint ξ).overObj :=
  yonedaEquiv
    ((chosenPresentation (fieldFiber f (FieldValuedPoint.residuePoint ξ))).atlas ≫
      fieldFiberToSpec f (FieldValuedPoint.residuePoint ξ))

/-- `genericFiberAtlasOverHom f ξ` is the Yoneda transpose of the atlas of `X_ξ`
composed with the structure morphism to `Spec κ(ξ)`. -/
theorem genericFiberAtlasOverHom_yoneda {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    [IsDecent Y] (f : X ⟶ Y) (ξ : Points Y) :
    yoneda.map (genericFiberAtlasOverHom f ξ) =
      (chosenPresentation (fieldFiber f (FieldValuedPoint.residuePoint ξ))).atlas ≫
        fieldFiberToSpec f (FieldValuedPoint.residuePoint ξ) :=
  sorry

/-- The two presentation restrictions agree on the composite of
`ΓSpecIso.inv` with the global-sections map of `genericFiberAtlasOverHom`. -/
theorem genericFiberGlobalSectionsMap_equalizes {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} [IsDecent Y] (f : X ⟶ Y) (ξ : Points Y) :
    ((Scheme.ΓSpecIso (Y.residueField ξ)).inv ≫
        (genericFiberAtlasOverHom f ξ).left.appTop) ≫
      (chosenPresentation (fieldFiber f (FieldValuedPoint.residuePoint ξ))).tAppTop =
    ((Scheme.ΓSpecIso (Y.residueField ξ)).inv ≫
        (genericFiberAtlasOverHom f ξ).left.appTop) ≫
      (chosenPresentation (fieldFiber f (FieldValuedPoint.residuePoint ξ))).sAppTop :=
  sorry

/-- The canonical ring map `κ(ξ) ⟶ Γ(X_ξ, 𝒪)` induced by the structure morphism
of the field-valued fibre of `f` at the residue-field point of `ξ`. -/
noncomputable def genericFiberGlobalSectionsMap {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} [IsDecent Y] (f : X ⟶ Y) (ξ : Points Y) :
    Y.residueField ξ ⟶
      globalSectionsRing (fieldFiber f (FieldValuedPoint.residuePoint ξ)) :=
  equalizer.lift
    ((Scheme.ΓSpecIso (Y.residueField ξ)).inv ≫
      (genericFiberAtlasOverHom f ξ).left.appTop)
    (genericFiberGlobalSectionsMap_equalizes f ξ)

/-- After comparison with the chosen atlas of the generic fibre,
`genericFiberGlobalSectionsMap f ξ` recovers the global-sections map of
`genericFiberAtlasOverHom f ξ`. -/
theorem genericFiberGlobalSectionsMap_comp_ι {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} [IsDecent Y] (f : X ⟶ Y) (ξ : Points Y) :
    genericFiberGlobalSectionsMap f ξ ≫
        globalSectionsRing_ι (fieldFiber f (FieldValuedPoint.residuePoint ξ)) =
      (Scheme.ΓSpecIso (Y.residueField ξ)).inv ≫
        (genericFiberAtlasOverHom f ξ).left.appTop :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Hom
