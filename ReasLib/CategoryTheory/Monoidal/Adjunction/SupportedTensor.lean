/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Monoidal.Adjunction.ProjectionFormula
public import Mathlib.CategoryTheory.CommSq
public import Mathlib.CategoryTheory.Functor.Currying
import Mathlib.Tactic.CrossRefAttribute

/-!
# Tensor products followed by a supported right adjoint

This file owns the two-adjunction construction used for tensor products with support.  The
left-hand adjunction supplies the projection formula, while the second adjunction supplies the
support functor.  Keeping the construction at this level avoids making geometric files choose a
model for restriction, tensor products, or supported sections.
-/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory

noncomputable section

universe uC uD vC vD

namespace CategoryTheory.Adjunction

variable {C : Type uC} [Category.{vC} C] [MonoidalCategory C]
variable {D : Type uD} [Category.{vD} D] [MonoidalCategory D]
variable {L : D ⥤ C} {P : C ⥤ D} {H : D ⥤ C}

section ExplicitTensor

variable {C₀ : Type uC} [Category.{vC} C₀]
variable {D₀ : Type uD} [Category.{vD} D₀]
variable {L₀ : D₀ ⥤ C₀} {P₀ : C₀ ⥤ D₀} {H₀ : D₀ ⥤ C₀}

namespace SupportTensor

/-- Take the support-adjunction mate of one ambient map for explicitly chosen binary functors.

This pointwise owner is the basic reusable API.  A family of ambient maps is not needed until a
natural transformation is being assembled, so downstream constructions can supply only the map at
the objects they are currently using. -/
@[stacks 0G75 "pointwise tensor support mate from explicit tensor functors"]
noncomputable def of
    (supportAdj : P₀ ⊣ H₀)
    (tensorC : C₀ ⥤ C₀ ⥤ C₀)
    (tensorD : D₀ ⥤ D₀ ⥤ D₀)
    (K M : D₀)
    (ambient :
      P₀.obj ((tensorC.obj (L₀.obj K)).obj (H₀.obj M)) ⟶
        (tensorD.obj K).obj M) :
    (tensorC.obj (L₀.obj K)).obj (H₀.obj M) ⟶
      H₀.obj ((tensorD.obj K).obj M) :=
  supportAdj.homEquiv _ _ ambient

/-- Transposing the pointwise explicit-functor support mate recovers its ambient map. -/
@[simp, stacks 0G75 "pointwise tensor support mate specification"]
theorem of_spec
    (supportAdj : P₀ ⊣ H₀)
    (tensorC : C₀ ⥤ C₀ ⥤ C₀)
    (tensorD : D₀ ⥤ D₀ ⥤ D₀)
    (K M : D₀)
    (ambient :
      P₀.obj ((tensorC.obj (L₀.obj K)).obj (H₀.obj M)) ⟶
        (tensorD.obj K).obj M) :
    (supportAdj.homEquiv
        ((tensorC.obj (L₀.obj K)).obj (H₀.obj M))
        ((tensorD.obj K).obj M)).symm
        (of supportAdj tensorC tensorD K M ambient) =
      ambient := sorry

/-- Apply the supporting left adjoint to the pointwise support mate and recover the ambient map. -/
@[stacks 0G75 "pointwise tensor support mate counit square"]
theorem of_comp_counit
    (supportAdj : P₀ ⊣ H₀)
    (tensorC : C₀ ⥤ C₀ ⥤ C₀)
    (tensorD : D₀ ⥤ D₀ ⥤ D₀)
    (K M : D₀)
    (ambient :
      P₀.obj ((tensorC.obj (L₀.obj K)).obj (H₀.obj M)) ⟶
        (tensorD.obj K).obj M) :
    P₀.map (of supportAdj tensorC tensorD K M ambient) ≫
        supportAdj.counit.app ((tensorD.obj K).obj M) =
      ambient := sorry

end SupportTensor

/-- Take the support-adjunction mate of an ambient map for explicitly chosen binary functors.

This variant does not require monoidal instances on either category.  It is the reusable owner for
derived tensor models represented by a bifunctor (for example a closed-subset derived category);
`SupportTensor.of` is the pointwise core, while this family form is a convenience bridge. -/
@[stacks 0G75 "tensor product with support from explicit tensor functors"]
noncomputable def supportTensorOfFunctors
    (supportAdj : P₀ ⊣ H₀)
    (tensorC : C₀ ⥤ C₀ ⥤ C₀)
    (tensorD : D₀ ⥤ D₀ ⥤ D₀)
    (ambient : ∀ K M : D₀,
      P₀.obj ((tensorC.obj (L₀.obj K)).obj (H₀.obj M)) ⟶
        (tensorD.obj K).obj M)
    (K M : D₀) :
    (tensorC.obj (L₀.obj K)).obj (H₀.obj M) ⟶
      H₀.obj ((tensorD.obj K).obj M) :=
  SupportTensor.of supportAdj tensorC tensorD K M (ambient K M)

/-- The mate specification for `supportTensorOfFunctors`. -/
@[stacks 0G75 "explicit tensor support mate specification"]
theorem supportTensorOfFunctors_spec
    (supportAdj : P₀ ⊣ H₀)
    (tensorC : C₀ ⥤ C₀ ⥤ C₀)
    (tensorD : D₀ ⥤ D₀ ⥤ D₀)
    (ambient : ∀ K M : D₀,
      P₀.obj ((tensorC.obj (L₀.obj K)).obj (H₀.obj M)) ⟶
        (tensorD.obj K).obj M)
    (K M : D₀) :
    (supportAdj.homEquiv
        ((tensorC.obj (L₀.obj K)).obj (H₀.obj M))
        ((tensorD.obj K).obj M)).symm
        (supportTensorOfFunctors supportAdj tensorC tensorD ambient K M) =
      ambient K M := sorry

/-- The counit square for `supportTensorOfFunctors`. -/
@[stacks 0G75 "explicit tensor support counit square"]
theorem supportTensorOfFunctors_commSq
    (supportAdj : P₀ ⊣ H₀)
    (tensorC : C₀ ⥤ C₀ ⥤ C₀)
    (tensorD : D₀ ⥤ D₀ ⥤ D₀)
    (ambient : ∀ K M : D₀,
      P₀.obj ((tensorC.obj (L₀.obj K)).obj (H₀.obj M)) ⟶
        (tensorD.obj K).obj M)
    (K M : D₀) :
    CommSq
      (P₀.map (supportTensorOfFunctors supportAdj tensorC tensorD ambient K M))
      (ambient K M)
      (supportAdj.counit.app ((tensorD.obj K).obj M))
      (𝟙 ((tensorD.obj K).obj M)) := sorry

/-- The equality form of `supportTensorOfFunctors_commSq`. -/
@[stacks 0G75 "explicit tensor support counit equation"]
theorem supportTensorOfFunctors_comp_counit
    (supportAdj : P₀ ⊣ H₀)
    (tensorC : C₀ ⥤ C₀ ⥤ C₀)
    (tensorD : D₀ ⥤ D₀ ⥤ D₀)
    (ambient : ∀ K M : D₀,
      P₀.obj ((tensorC.obj (L₀.obj K)).obj (H₀.obj M)) ⟶
        (tensorD.obj K).obj M)
    (K M : D₀) :
    P₀.map (supportTensorOfFunctors supportAdj tensorC tensorD ambient K M) ≫
        supportAdj.counit.app ((tensorD.obj K).obj M) =
      ambient K M := sorry

namespace supportTensorOfFunctors

/-- Mate an ambient natural transformation to a supported tensor natural transformation for
explicitly chosen bifunctors. -/
@[stacks 0G75 "explicit tensor support natural transformation"]
noncomputable def natTrans
    (supportAdj : P₀ ⊣ H₀)
    (tensorC : C₀ ⥤ C₀ ⥤ C₀)
    (tensorD : D₀ ⥤ D₀ ⥤ D₀)
    (ambient :
      (Functor.prod L₀ H₀ ⋙ Functor.uncurry.obj tensorC) ⋙ P₀ ⟶
        Functor.uncurry.obj tensorD) :
    Functor.prod L₀ H₀ ⋙ Functor.uncurry.obj tensorC ⟶
      Functor.uncurry.obj tensorD ⋙ H₀ where
  app KM := SupportTensor.of supportAdj tensorC tensorD KM.1 KM.2
    (ambient.app (KM.1, KM.2))
  naturality := sorry

/-- The component of `supportTensorOfFunctors.natTrans` is the pointwise explicit tensor mate. -/
@[stacks 0G75 "explicit tensor support natural transformation component"]
theorem natTrans_app
    (supportAdj : P₀ ⊣ H₀)
    (tensorC : C₀ ⥤ C₀ ⥤ C₀)
    (tensorD : D₀ ⥤ D₀ ⥤ D₀)
    (ambient :
      (Functor.prod L₀ H₀ ⋙ Functor.uncurry.obj tensorC) ⋙ P₀ ⟶
        Functor.uncurry.obj tensorD)
    (K M : D₀) :
    (supportTensorOfFunctors.natTrans supportAdj tensorC tensorD ambient).app (K, M) =
      SupportTensor.of supportAdj tensorC tensorD K M (ambient.app (K, M)) := rfl

end supportTensorOfFunctors

end ExplicitTensor

namespace SupportTensor

/-- Take the support-adjunction mate of one ambient tensor map in monoidal categories.

This is the monoidal specialization of `SupportTensor.of`; the ambient morphism is pointwise data,
so no full two-variable family is forced on callers. -/
@[stacks 0G75 "pointwise tensor support mate"]
noncomputable def ofMonoidal
    (supportAdj : P ⊣ H)
    (K M : D)
    (ambient : P.obj ((L.obj K) ⊗ (H.obj M)) ⟶ K ⊗ M) :
    (L.obj K) ⊗ (H.obj M) ⟶ H.obj (K ⊗ M) :=
  supportAdj.homEquiv _ _ ambient

/-- Transposing the pointwise monoidal support mate recovers its ambient tensor map. -/
@[simp, stacks 0G75 "pointwise tensor support mate specification"]
theorem ofMonoidal_spec
    (supportAdj : P ⊣ H)
    (K M : D)
    (ambient : P.obj ((L.obj K) ⊗ (H.obj M)) ⟶ K ⊗ M) :
    (supportAdj.homEquiv ((L.obj K) ⊗ (H.obj M)) (K ⊗ M)).symm
        (ofMonoidal supportAdj K M ambient) = ambient := sorry

/-- Applying the supporting left adjoint to the pointwise monoidal support mate recovers its map. -/
@[stacks 0G75 "pointwise tensor support mate counit equation"]
theorem ofMonoidal_comp_counit
    (supportAdj : P ⊣ H)
    (K M : D)
    (ambient : P.obj ((L.obj K) ⊗ (H.obj M)) ⟶ K ⊗ M) :
    P.map (ofMonoidal supportAdj K M ambient) ≫ supportAdj.counit.app (K ⊗ M) = ambient := sorry

end SupportTensor

/-- Take the mate of an explicitly supplied ambient tensor map under the support adjunction.

The ambient map is data rather than a typeclass assumption.  This is the source-independent
interface for tensor products with support; `SupportTensor.ofMonoidal` is the pointwise owner and
this family form is a convenience bridge. -/
@[stacks 0G75 "tensor product with support from an ambient map"]
noncomputable def supportTensorOf
    (supportAdj : P ⊣ H)
    (ambient : ∀ K M : D,
      P.obj ((L.obj K) ⊗ (H.obj M)) ⟶ K ⊗ M)
    (K M : D) :
    (L.obj K) ⊗ (H.obj M) ⟶ H.obj (K ⊗ M) :=
  SupportTensor.ofMonoidal supportAdj K M (ambient K M)

/-- The mate specification for `supportTensorOf`. -/
@[stacks 0G75 "tensor product with support from an ambient map specification"]
theorem supportTensorOf_spec
    (supportAdj : P ⊣ H)
    (ambient : ∀ K M : D,
      P.obj ((L.obj K) ⊗ (H.obj M)) ⟶ K ⊗ M)
    (K M : D) :
    (supportAdj.homEquiv ((L.obj K) ⊗ (H.obj M)) (K ⊗ M)).symm
        (supportTensorOf supportAdj ambient K M) = ambient K M := sorry

/-- Applying the supporting left adjoint to the mate of an ambient map and then the counit
recovers that ambient map. -/
@[stacks 0G75 "tensor product with support from an ambient map counit square"]
theorem supportTensorOf_commSq
    (supportAdj : P ⊣ H)
    (ambient : ∀ K M : D,
      P.obj ((L.obj K) ⊗ (H.obj M)) ⟶ K ⊗ M)
    (K M : D) :
    CommSq
      (P.map (supportTensorOf supportAdj ambient K M))
      (ambient K M)
      (supportAdj.counit.app (K ⊗ M))
      (𝟙 (K ⊗ M)) := sorry

/-- Equality form of `supportTensorOf_commSq`. -/
@[stacks 0G75 "tensor product with support from an ambient map counit equation"]
theorem supportTensorOf_comp_counit
    (supportAdj : P ⊣ H)
    (ambient : ∀ K M : D,
      P.obj ((L.obj K) ⊗ (H.obj M)) ⟶ K ⊗ M)
    (K M : D) :
    P.map (supportTensorOf supportAdj ambient K M) ≫ supportAdj.counit.app (K ⊗ M) =
      ambient K M := sorry

section

variable (pullAdj : L ⊣ P) (supportAdj : P ⊣ H)
variable [L.OplaxMonoidal] [pullAdj.ProjectionFormula]

/-- The ambient tensor map underlying the tensor product with support. -/
@[stacks 0G75 "pushforward-side tensor map with support"]
noncomputable def supportTensorPush (K M : D) :
    P.obj ((L.obj K) ⊗ (H.obj M)) ⟶ K ⊗ M :=
  (pullAdj.projectionFormulaIso K (H.obj M)).inv ≫
    (𝟙 K ⊗ₘ supportAdj.counit.app M)

/-- The canonical tensor product with support, obtained by transposing the ambient tensor map. -/
@[stacks 0G75 "tensor product with support"]
noncomputable def supportTensor (K M : D) :
    (L.obj K) ⊗ (H.obj M) ⟶ H.obj (K ⊗ M) :=
  SupportTensor.ofMonoidal supportAdj K M (supportTensorPush pullAdj supportAdj K M)

/-- The ambient tensor maps form a natural transformation in both ambient arguments. -/
@[stacks 0G75 "pushforward-side tensor map with support"]
noncomputable def supportTensorPushNatTrans :
    (Functor.prod L H ⋙ MonoidalCategory.tensor C) ⋙ P ⟶
      MonoidalCategory.tensor D where
  app KM := supportTensorPush pullAdj supportAdj KM.1 KM.2
  naturality _ _ _ := sorry

/-- Tensor products with support form a natural transformation in both ambient arguments. -/
@[stacks 0G75 "tensor product with support natural transformation"]
noncomputable def supportTensorNatTrans :
    Functor.prod L H ⋙ MonoidalCategory.tensor C ⟶
      MonoidalCategory.tensor D ⋙ H where
  app KM := supportTensor pullAdj supportAdj KM.1 KM.2
  naturality _ _ _ := sorry

/-- For a fixed ambient left factor, tensor products with support are natural in the supported
right factor. -/
@[stacks 0G75 "fixed-left tensor product with support"]
noncomputable def supportTensorLeftNatTrans (K : D) :
    H ⋙ tensorLeft (L.obj K) ⟶ tensorLeft K ⋙ H where
  app M := supportTensor pullAdj supportAdj K M
  naturality _ _ _ := sorry

/-- For a fixed supported right factor, tensor products with support are natural in the ambient
left factor. -/
@[stacks 0G75 "fixed-right tensor product with support"]
noncomputable def supportTensorRightNatTrans (M : D) :
    L ⋙ tensorRight (H.obj M) ⟶ tensorRight M ⋙ H where
  app K := supportTensor pullAdj supportAdj K M
  naturality _ _ _ := sorry

/-- The component of `supportTensorPushNatTrans` is the ambient tensor map. -/
@[simp, stacks 0G75 "pushforward-side tensor map component"]
theorem supportTensorPushNatTrans_app (K M : D) :
    (supportTensorPushNatTrans pullAdj supportAdj).app (K, M) =
      supportTensorPush pullAdj supportAdj K M := sorry

/-- The component of `supportTensorNatTrans` is the tensor product with support. -/
@[simp, stacks 0G75 "tensor product with support component"]
theorem supportTensorNatTrans_app (K M : D) :
    (supportTensorNatTrans pullAdj supportAdj).app (K, M) =
      supportTensor pullAdj supportAdj K M := sorry

/-- The component of the fixed-left tensor-with-support transformation is `supportTensor`. -/
@[simp, stacks 0G75 "fixed-left tensor product with support component"]
theorem supportTensorLeftNatTrans_app (K M : D) :
    (supportTensorLeftNatTrans pullAdj supportAdj K).app M =
      supportTensor pullAdj supportAdj K M := sorry

/-- The component of the fixed-right tensor-with-support transformation is `supportTensor`. -/
@[simp, stacks 0G75 "fixed-right tensor product with support component"]
theorem supportTensorRightNatTrans_app (K M : D) :
    (supportTensorRightNatTrans pullAdj supportAdj M).app K =
      supportTensor pullAdj supportAdj K M := sorry

/-- The mate specification for `supportTensor`. -/
@[stacks 0G75 "tensor product with support mate specification"]
theorem supportTensor_spec (K M : D) :
    (supportAdj.homEquiv ((L.obj K) ⊗ (H.obj M)) (K ⊗ M)).symm
        (supportTensor pullAdj supportAdj K M) =
      supportTensorPush pullAdj supportAdj K M := sorry

/-- Applying the supporting left adjoint to `supportTensor` and then its counit recovers the
ambient tensor map. -/
@[stacks 0G75 "tensor product with support counit square"]
theorem supportTensor_commSq (K M : D) :
    CommSq
      (P.map (supportTensor pullAdj supportAdj K M))
      (supportTensorPush pullAdj supportAdj K M)
      (supportAdj.counit.app (K ⊗ M))
      (𝟙 (K ⊗ M)) := sorry

/-- Equality form of the counit square for `supportTensor`. -/
@[stacks 0G75 "tensor product with support counit equation"]
theorem supportTensor_comp_counit (K M : D) :
    P.map (supportTensor pullAdj supportAdj K M) ≫
        supportAdj.counit.app (K ⊗ M) =
      supportTensorPush pullAdj supportAdj K M := sorry

end

end CategoryTheory.Adjunction
