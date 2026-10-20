/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.ExtensionByZero.Composition
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.GlobalSections
public import Mathlib.CategoryTheory.Linear.FunctorCategory
public import Mathlib.CategoryTheory.Linear.Yoneda
public import Mathlib.CategoryTheory.Sites.ConstantSheaf

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
open CategoryTheory.Linear CategoryTheory.Sheaf
open AlgebraicGeometry AlgebraicGeometry.Scheme Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

variable (Λ : Type u) [CommRing Λ]
variable [∀ U : Scheme.{u}, HasWeakSheafify U.smallEtaleTopology (ModuleCat.{u} Λ)]
/-- The constant étale sheaf of `Λ`-modules on a scheme. -/
def etaleConstantModule (S : Scheme.{u}) :
    Sheaf S.smallEtaleTopology (ModuleCat.{u} Λ) :=
  (constantSheaf S.smallEtaleTopology (ModuleCat.{u} Λ)).obj (ModuleCat.of Λ Λ)

/-- The constant sheaf of `Λ`-modules is the sheafification of the constant
presheaf on `ModuleCat.of Λ Λ`. -/
theorem etaleConstantModule_def (S : Scheme.{u}) :
    etaleConstantModule Λ S =
      (constantSheaf S.smallEtaleTopology (ModuleCat.{u} Λ)).obj
        (ModuleCat.of Λ Λ) :=
  rfl

section ExtensionByZero

variable [∀ (U V : Scheme.{u}) (f : U ⟶ V) [Etale f]
    (F : U.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ),
  (etaleRestriction f).op.HasLeftKanExtension F]

/-- Extension by zero of the constant `Λ`-module sheaf along an étale morphism. -/
def etaleExtensionByZeroConstant {U S : Scheme.{u}} (j : U ⟶ S) [Etale j] :
    Sheaf S.smallEtaleTopology (ModuleCat.{u} Λ) :=
  (etaleExtensionByZero j (ModuleCat.{u} Λ)).obj (etaleConstantModule Λ U)

/-- Evaluating `j_! Λ` applies étale extension by zero to the constant sheaf. -/
theorem etaleExtensionByZeroConstant_obj {U S : Scheme.{u}} (j : U ⟶ S)
    [Etale j] :
    etaleExtensionByZeroConstant Λ j =
      (etaleExtensionByZero j (ModuleCat.{u} Λ)).obj (etaleConstantModule Λ U) :=
  rfl

/-- Bundled extension by zero of the constant sheaf along an object of the
small étale site. -/
def etaleExtensionByZeroConstantOver {S : Scheme.{u}} (U : S.Etale) :
    Sheaf S.smallEtaleTopology (ModuleCat.{u} Λ) :=
  @etaleExtensionByZeroConstant Λ _ _ _ U.left S U.hom U.prop

/-- Bundled `j_! Λ` is extension by zero of the constant sheaf along `U.hom`. -/
theorem etaleExtensionByZeroConstantOver_obj {S : Scheme.{u}} (U : S.Etale) :
    etaleExtensionByZeroConstantOver Λ U =
      @etaleExtensionByZeroConstant Λ _ _ _ U.left S U.hom U.prop :=
  rfl

/-- The canonical map from the constant sheaf on the source to the restriction
of the constant sheaf on the target. -/
def etaleConstantToRestriction {U S : Scheme.{u}} (j : U ⟶ S) [Etale j] :
    etaleConstantModule Λ U ⟶
      (etaleRestrictionSheaf j (ModuleCat.{u} Λ)).obj (etaleConstantModule Λ S) :=
  ((sheafificationAdjunction U.smallEtaleTopology (ModuleCat.{u} Λ)).homEquiv
      ((Functor.const U.Etaleᵒᵖ).obj (ModuleCat.of Λ Λ))
      ((etaleRestrictionSheaf j (ModuleCat.{u} Λ)).obj
        (etaleConstantModule Λ S))).symm
    ((Functor.constCompWhiskeringLeftIso
        (J := U.Etaleᵒᵖ) (D := S.Etaleᵒᵖ) (C := ModuleCat.{u} Λ)
        (etaleRestriction j).op).inv.app (ModuleCat.of Λ Λ) ≫
      whiskerLeft (etaleRestriction j).op
        (toSheafify S.smallEtaleTopology
          ((Functor.const S.Etaleᵒᵖ).obj (ModuleCat.of Λ Λ))))

/-- The étale trace `Tr_j : j_! Λ ⟶ Λ` obtained from the extension-by-zero
counit after identifying the restriction of the constant sheaf. -/
def etaleTrace {U S : Scheme.{u}} (j : U ⟶ S) [Etale j] :
    etaleExtensionByZeroConstant Λ j ⟶ etaleConstantModule Λ S :=
  ((etaleExtensionByZero_adjunction j (ModuleCat.{u} Λ)).homEquiv
      (etaleConstantModule Λ U) (etaleConstantModule Λ S)).symm
    (etaleConstantToRestriction Λ j)

/-- The étale trace is the adjunct of the canonical comparison of constant
sheaves. -/
theorem etaleTrace_spec {U S : Scheme.{u}} (j : U ⟶ S) [Etale j] :
    etaleTrace Λ j =
      ((etaleExtensionByZero_adjunction j (ModuleCat.{u} Λ)).homEquiv
          (etaleConstantModule Λ U) (etaleConstantModule Λ S)).symm
        (etaleConstantToRestriction Λ j) :=
  rfl

/-- The trace-induced map between extensions by zero along a morphism of
objects of the small étale site. -/
def etaleTraceOver {S : Scheme.{u}} {U U' : S.Etale} (φ : U ⟶ U') :
    etaleExtensionByZeroConstantOver Λ U ⟶
      etaleExtensionByZeroConstantOver Λ U' :=
  eqToHom (by
    unfold etaleExtensionByZeroConstantOver etaleExtensionByZeroConstant
    congr 2
    exact (MorphismProperty.Over.w φ).symm) ≫
  (@etaleExtensionByZeroCompIso U.left U'.left S φ.left U'.hom
      inferInstance U'.prop Λ _ _ _ _ _ _).inv.app
    (etaleConstantModule Λ U.left) ≫
  (@etaleExtensionByZero U'.left S U'.hom U'.prop (ModuleCat.{u} Λ) _ _ _).map
    (etaleTrace Λ φ.left)

/-- The trace-induced map of an identity is the identity. -/
theorem etaleTraceOver_id {S : Scheme.{u}} (U : S.Etale) :
    etaleTraceOver Λ (𝟙 U) = 𝟙 (etaleExtensionByZeroConstantOver Λ U) :=
  sorry

/-- Trace-induced maps respect composition of morphisms of étale objects. -/
theorem etaleTraceOver_comp {S : Scheme.{u}} {U U' U'' : S.Etale}
    (φ : U ⟶ U') (ψ : U' ⟶ U'') :
    etaleTraceOver Λ φ ≫ etaleTraceOver Λ ψ = etaleTraceOver Λ (φ ≫ ψ) :=
  sorry

/-- The extension-by-zero adjunction map preserves addition on Hom groups. -/
theorem etaleExtensionByZeroAdjunctionHomModule_map_add
    {U S : Scheme.{u}} (j : U ⟶ S) [h : Etale j]
    (F : Sheaf U.smallEtaleTopology (ModuleCat.{u} Λ))
    (G : Sheaf S.smallEtaleTopology (ModuleCat.{u} Λ))
    (φ ψ : (etaleExtensionByZero j (ModuleCat.{u} Λ)).obj F ⟶ G) :
    (etaleExtensionByZero_adjunction j (ModuleCat.{u} Λ)).homEquiv F G (φ + ψ) =
      (etaleExtensionByZero_adjunction j (ModuleCat.{u} Λ)).homEquiv F G φ +
      (etaleExtensionByZero_adjunction j (ModuleCat.{u} Λ)).homEquiv F G ψ :=
  sorry

/-- The extension-by-zero adjunction map preserves scalar multiplication. -/
theorem etaleExtensionByZeroAdjunctionHomModule_map_smul
    {U S : Scheme.{u}} (j : U ⟶ S) [h : Etale j]
    (F : Sheaf U.smallEtaleTopology (ModuleCat.{u} Λ))
    (G : Sheaf S.smallEtaleTopology (ModuleCat.{u} Λ)) (a : Λ)
    (φ : (etaleExtensionByZero j (ModuleCat.{u} Λ)).obj F ⟶ G) :
    (etaleExtensionByZero_adjunction j (ModuleCat.{u} Λ)).homEquiv F G (a • φ) =
      a • (etaleExtensionByZero_adjunction j (ModuleCat.{u} Λ)).homEquiv F G φ :=
  sorry

/-- The `Λ`-linear map on Hom-modules induced by `j_! ⊣ j^*`. -/
def etaleExtensionByZeroAdjunctionHomModule
    {U S : Scheme.{u}} (j : U ⟶ S) [h : Etale j]
    (F : Sheaf U.smallEtaleTopology (ModuleCat.{u} Λ))
    (G : Sheaf S.smallEtaleTopology (ModuleCat.{u} Λ)) :
    ((linearYoneda Λ
          (Sheaf S.smallEtaleTopology (ModuleCat.{u} Λ))).obj G).obj
        (op ((etaleExtensionByZero j (ModuleCat.{u} Λ)).obj F)) ⟶
      ((linearYoneda Λ
          (Sheaf U.smallEtaleTopology (ModuleCat.{u} Λ))).obj
        ((etaleRestrictionSheaf j (ModuleCat.{u} Λ)).obj G)).obj
        (op F) :=
  ModuleCat.ofHom
    { toFun := (etaleExtensionByZero_adjunction j (ModuleCat.{u} Λ)).homEquiv F G
      map_add' := etaleExtensionByZeroAdjunctionHomModule_map_add Λ j F G
      map_smul' := etaleExtensionByZeroAdjunctionHomModule_map_smul Λ j F G }

/-- The Hom-module map of `j_! ⊣ j^*` is the adjunction hom-equivalence. -/
theorem etaleExtensionByZeroAdjunctionHomModule_spec
    {U S : Scheme.{u}} (j : U ⟶ S) [h : Etale j]
    (F : Sheaf U.smallEtaleTopology (ModuleCat.{u} Λ))
    (G : Sheaf S.smallEtaleTopology (ModuleCat.{u} Λ))
    (φ : (etaleExtensionByZero j (ModuleCat.{u} Λ)).obj F ⟶ G) :
    etaleExtensionByZeroAdjunctionHomModule Λ j F G φ =
      (etaleExtensionByZero_adjunction j (ModuleCat.{u} Λ)).homEquiv F G φ :=
  rfl

end ExtensionByZero

/-- Postcomposition with an étale structural morphism sends the identity
étale object to the original object, up to the canonical isomorphism. -/
def etaleRestriction_identity {S : Scheme.{u}} (U : S.Etale) :
    (@etaleRestriction U.left S U.hom U.prop).obj (globalEtale U.left) ≅ U :=
  MorphismProperty.Over.isoMk (Iso.refl _) (by
    change 𝟙 U.left ≫ U.hom = 𝟙 U.left ≫ U.hom
    rfl)

/-- The identity-restriction comparison has identity underlying morphism. -/
theorem etaleRestriction_identity_hom_left {S : Scheme.{u}} (U : S.Etale) :
    (etaleRestriction_identity U).hom.left = 𝟙 U.left :=
  rfl

/-- Evaluate a map from the constant module sheaf at the sheafified unit
on the identity étale object, then transport the resulting section to `U`. -/
def etaleSheafEvalUnitModule {S : Scheme.{u}} (U : S.Etale)
    (G : Sheaf S.smallEtaleTopology (ModuleCat.{u} Λ))
    (φ : etaleConstantModule Λ U.left ⟶
      (@etaleRestrictionSheaf U.left S U.hom U.prop (ModuleCat.{u} Λ) _).obj G) :
    G.obj.obj (op U) :=
  G.obj.map (etaleRestriction_identity U).inv.op
    (ConcreteCategory.hom (C := ModuleCat.{u} Λ)
      ((Sheaf.homEquiv φ).app (op (globalEtale U.left)))
      (ConcreteCategory.hom (C := ModuleCat.{u} Λ)
        ((toSheafify U.left.smallEtaleTopology
          ((Functor.const U.left.Etaleᵒᵖ).obj (ModuleCat.of Λ Λ))).app
            (op (globalEtale U.left))) (1 : Λ)))

/-- Unit-section evaluation applies the map to the sheafification of `1` and
then uses the identity-restriction comparison. -/
theorem etaleSheafEvalUnitModule_spec {S : Scheme.{u}} (U : S.Etale)
    (G : Sheaf S.smallEtaleTopology (ModuleCat.{u} Λ))
    (φ : etaleConstantModule Λ U.left ⟶
      (@etaleRestrictionSheaf U.left S U.hom U.prop (ModuleCat.{u} Λ) _).obj G) :
    etaleSheafEvalUnitModule Λ U G φ =
      G.obj.map (etaleRestriction_identity U).inv.op
        (ConcreteCategory.hom (C := ModuleCat.{u} Λ)
          ((Sheaf.homEquiv φ).app (op (globalEtale U.left)))
          (ConcreteCategory.hom (C := ModuleCat.{u} Λ)
            ((toSheafify U.left.smallEtaleTopology
              ((Functor.const U.left.Etaleᵒᵖ).obj (ModuleCat.of Λ Λ))).app
                (op (globalEtale U.left))) (1 : Λ))) :=
  rfl

end AlgebraicGeometry.Scheme.Etale

end
