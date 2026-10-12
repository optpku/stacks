/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import stacks_project.Chap66.Lemma_66_25_4_Normal
public import stacks_project.Chap67.Definition_67_40_1_Proper
public import stacks_project.Chap67.Definition_67_48_3_IntegralClosure
public import stacks_project.Chap67.Lemma_67_48_6_Reduced
public import stacks_project.Chap68.Definition_68_11_2_ResidueField
public import stacks_project.Chap68.Definition_68_22_1_GenericPoints
public import stacks_project.Chap68.Lemma_68_18_6_Fibre
public import stacks_project.Chap69.Situation_69_16_1_GlobalSections
public import stacks_project.Chap72.Definition_72_4_1_Integral
public import stacks_project.Chap76.Theorem_76_36_4_Stein_factorization_Noetherian_case_GeometricallyConnected

/-!
# Generic-fibre global sections towards a normal integral target

A proper morphism of algebraic spaces to a normal integral space, with reduced
source, generic points over the generic point of the target, and
`H^0(X_ξ, 𝒪) = κ(ξ)`, pushes the structure sheaf isomorphically and has
geometrically connected fibres.
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

/-- Lemma 76.36.6 (1): if `f : X ⟶ Y` is a proper morphism of algebraic spaces,
`Y` is integral and normal with generic point `ξ`, `X` is reduced, every generic
point of an irreducible component of `|X|` maps to `ξ`, and
`H^0(X_ξ, 𝒪) = κ(ξ)`, then `f_* 𝒪_X = 𝒪_Y`. -/
@[stacks 0AYI]
theorem commRingStructureSheafMap_isIso_of_genericFiberGlobalSections
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [Proper f] [IsIntegral Y] [IsNormal Y] [IsReduced X]
    {ξ : Points Y} (hξ : ξ ∈ genericPoints Y)
    (h_generic : ∀ ⦃x : Points X⦄, x ∈ genericPoints X → Points.map f x = ξ)
    (hΓ : IsIso (genericFiberGlobalSectionsMap f ξ)) :
    IsIso (commRingStructureSheafMap f) :=
  sorry

/-- Lemma 76.36.6 (2): under the same hypotheses, `f` has geometrically connected
fibres. -/
@[stacks 0AYI]
theorem hasConnectedGeometricFibres_of_genericFiberGlobalSections
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [Proper f] [IsIntegral Y] [IsNormal Y] [IsReduced X]
    {ξ : Points Y} (hξ : ξ ∈ genericPoints Y)
    (h_generic : ∀ ⦃x : Points X⦄, x ∈ genericPoints X → Points.map f x = ξ)
    (hΓ : IsIso (genericFiberGlobalSectionsMap f ξ)) :
    HasConnectedGeometricFibres f :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Hom
