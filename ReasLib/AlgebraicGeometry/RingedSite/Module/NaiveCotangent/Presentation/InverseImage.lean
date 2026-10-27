/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.InverseImage
public import ReasLib.AlgebraicGeometry.RingedSite.Module.NaiveCotangent
import Mathlib.Tactic.CrossRefAttribute

/-!
# Inverse image of canonical polynomial presentations

This file constructs the comparison between the inverse image of a canonical polynomial
presentation and the canonical polynomial presentation of the inverse-image ring map.  It is the
commutative-ring data layer used by inverse-image comparisons of conormal objects and cotangent
complexes.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Sheaf
open SheafOfModules.RingedSite.InverseImage

noncomputable section

universe u

namespace SheafOfModules
namespace RingedSite
namespace NaiveCotangent
variable {C D : Type u} [Category.{u} C] [Category.{u} D]
variable {J : GrothendieckTopology C} {K : GrothendieckTopology D}
variable (F : C ⥤ D) [F.IsContinuous J K]
variable [HasWeakSheafify K CommRingCat.{u}]
variable [∀ P : Cᵒᵖ ⥤ CommRingCat.{u}, F.op.HasLeftKanExtension P]
variable {O₁ O₂ : Sheaf J CommRingCat.{u}}

/-- The inverse-image morphism of commutative ring sheaves. -/
abbrev inverseImageMap (f : O₁ ⟶ O₂) :
    (ringPullback (J := J) (K := K) F).obj O₁ ⟶
      (ringPullback (J := J) (K := K) F).obj O₂ :=
  (ringPullback (J := J) (K := K) F).map f

/-- The pulled-back ring map, bundled as an algebra object over the pulled-back source. -/
abbrev inverseImageUnder (f : O₁ ⟶ O₂) :
    Under ((ringPullback (J := J) (K := K) F).obj O₁) :=
  Under.mk (inverseImageMap (J := J) (K := K) F f)

namespace Presentation
namespace InverseImage
/-- The map on generators used to transpose the pulled canonical polynomial presentation. -/
noncomputable def generatorAdjoint (f : O₁ ⟶ O₂) :
    FreeAlgebra.Presentation.generators (Under.mk f) ⟶
      (sheafForget J).obj
        ((F.sheafPushforwardContinuous CommRingCat.{u} J K).obj
          (FreeAlgebra.Presentation.underlying
            ((ringPullback (J := J) (K := K) F).obj O₁)
            (inverseImageUnder (J := J) (K := K) F f))) :=
  (sheafForget J).map (ringUnit (J := J) (K := K) F O₂) ≫
    (F.sheafPushforwardContinuous (Type u) J K).map
      (FreeAlgebra.Presentation.generator
        ((ringPullback (J := J) (K := K) F).obj O₁)
        (inverseImageUnder (J := J) (K := K) F f))

/-- The adjoint-side map from the original canonical polynomial presentation to the pushforward
of the canonical presentation of the pulled-back ring map. -/
noncomputable def adjoint (f : O₁ ⟶ O₂) :
    FreeAlgebra.Presentation.underlying O₁ (Under.mk f) ⟶
      (F.sheafPushforwardContinuous CommRingCat.{u} J K).obj
        (FreeAlgebra.Presentation.underlying
          ((ringPullback (J := J) (K := K) F).obj O₁)
          (inverseImageUnder (J := J) (K := K) F f)) :=
  (FreeAlgebra.evaluation
    (Under.mk
      (ringUnit (J := J) (K := K) F O₁ ≫
        (F.sheafPushforwardContinuous CommRingCat.{u} J K).map
          (FreeAlgebra.Presentation.base
            ((ringPullback (J := J) (K := K) F).obj O₁)
            (inverseImageUnder (J := J) (K := K) F f))))
    (FreeAlgebra.Presentation.generators (Under.mk f))
    (generatorAdjoint (J := J) (K := K) F f)).right

/-- On bracket generators, the adjoint-side presentation map is the map used in its free-algebra
construction. -/
theorem adjoint_generator (f : O₁ ⟶ O₂) :
    FreeAlgebra.Presentation.generator O₁ (Under.mk f) ≫
        (sheafForget J).map (adjoint (J := J) (K := K) F f) =
      generatorAdjoint (J := J) (K := K) F f := sorry

/-- The adjoint-side presentation map is compatible with the coefficient morphisms. -/
theorem adjoint_base (f : O₁ ⟶ O₂) :
    FreeAlgebra.Presentation.base O₁ (Under.mk f) ≫
        adjoint (J := J) (K := K) F f =
      ringUnit (J := J) (K := K) F O₁ ≫
        (F.sheafPushforwardContinuous CommRingCat.{u} J K).map
          (FreeAlgebra.Presentation.base
            ((ringPullback (J := J) (K := K) F).obj O₁)
            (inverseImageUnder (J := J) (K := K) F f)) := sorry

/-- The adjoint-side presentation map commutes with evaluation to the presented ring sheaf. -/
theorem adjoint_target (f : O₁ ⟶ O₂) :
    adjoint (J := J) (K := K) F f ≫
        (F.sheafPushforwardContinuous CommRingCat.{u} J K).map
          (FreeAlgebra.Presentation.map
            ((ringPullback (J := J) (K := K) F).obj O₁)
            (inverseImageUnder (J := J) (K := K) F f)) =
      FreeAlgebra.Presentation.map O₁ (Under.mk f) ≫
        ringUnit (J := J) (K := K) F O₂ := sorry

/-- The adjoint-side presentation map and inverse-image unit form a commutative evaluation
square. -/
theorem adjoint_square (f : O₁ ⟶ O₂) :
    CommSq (adjoint (J := J) (K := K) F f)
      (FreeAlgebra.Presentation.map O₁ (Under.mk f))
      ((F.sheafPushforwardContinuous CommRingCat.{u} J K).map
        (FreeAlgebra.Presentation.map
          ((ringPullback (J := J) (K := K) F).obj O₁)
          (inverseImageUnder (J := J) (K := K) F f)))
      (ringUnit (J := J) (K := K) F O₂) := ⟨adjoint_target F f⟩

/-- The canonical comparison from the inverse image of the original polynomial presentation to
the canonical polynomial presentation of the inverse-image ring map. -/
@[stacks 08TM "polynomial-presentation comparison"]
noncomputable def comparison (f : O₁ ⟶ O₂) :
    (ringPullback (J := J) (K := K) F).obj
        (FreeAlgebra.Presentation.underlying O₁ (Under.mk f)) ⟶
      FreeAlgebra.Presentation.underlying
        ((ringPullback (J := J) (K := K) F).obj O₁)
        (inverseImageUnder (J := J) (K := K) F f) :=
  ((F.sheafAdjunctionContinuous CommRingCat.{u} J K).homEquiv _ _).symm
    (adjoint (J := J) (K := K) F f)

/-- The presentation comparison commutes with the coefficient morphisms. -/
theorem comparison_base (f : O₁ ⟶ O₂) :
    (ringPullback (J := J) (K := K) F).map
          (FreeAlgebra.Presentation.base O₁ (Under.mk f)) ≫
        comparison (J := J) (K := K) F f =
      FreeAlgebra.Presentation.base
        ((ringPullback (J := J) (K := K) F).obj O₁)
        (inverseImageUnder (J := J) (K := K) F f) := sorry

/-- The presentation comparison commutes with evaluation to the presented ring sheaves. -/
theorem comparison_target (f : O₁ ⟶ O₂) :
    comparison (J := J) (K := K) F f ≫
        FreeAlgebra.Presentation.map
          ((ringPullback (J := J) (K := K) F).obj O₁)
          (inverseImageUnder (J := J) (K := K) F f) =
      (ringPullback (J := J) (K := K) F).map
        (FreeAlgebra.Presentation.map O₁ (Under.mk f)) := sorry

/-- The inverse-image generator map obtained by transporting the original bracket map
through inverse image of the underlying sheaves of sets. -/
private noncomputable def inverseGenerator [RepresentablyFlat F] (f : O₁ ⟶ O₂) :
    (sheafForget K).obj ((ringPullback (J := J) (K := K) F).obj O₂) ⟶
      (sheafForget K).obj ((ringPullback (J := J) (K := K) F).obj
        (FreeAlgebra.Presentation.underlying O₁ (Under.mk f))) :=
  ((Functor.sheafPullback.compSheafComposeIso F (CategoryTheory.forget CommRingCat.{u}) J K).app O₂).hom ≫
    (F.sheafPullback (Type u) J K).map
      (FreeAlgebra.Presentation.generator O₁ (Under.mk f)) ≫
    ((Functor.sheafPullback.compSheafComposeIso F (CategoryTheory.forget CommRingCat.{u}) J K).app
      (FreeAlgebra.Presentation.underlying O₁ (Under.mk f))).inv

/-- The reverse polynomial comparison evaluates brackets at the inverse image of the original
bracket inclusion, with coefficients given by the pulled-back base map. -/
@[no_expose] noncomputable def comparisonInv [RepresentablyFlat F] (f : O₁ ⟶ O₂) :
    FreeAlgebra.Presentation.underlying
        ((ringPullback (J := J) (K := K) F).obj O₁)
        (inverseImageUnder (J := J) (K := K) F f) ⟶
      (ringPullback (J := J) (K := K) F).obj
        (FreeAlgebra.Presentation.underlying O₁ (Under.mk f)) :=
  (FreeAlgebra.evaluation
    (Under.mk ((ringPullback (J := J) (K := K) F).map
      (FreeAlgebra.Presentation.base O₁ (Under.mk f))))
    (FreeAlgebra.Presentation.generators (inverseImageUnder (J := J) (K := K) F f))
    (inverseGenerator (J := J) (K := K) F f)).right

/-- The reverse polynomial comparison respects the coefficient map and evaluation. -/
theorem comparisonInv_laws [RepresentablyFlat F] (f : O₁ ⟶ O₂) :
    FreeAlgebra.Presentation.base
        ((ringPullback (J := J) (K := K) F).obj O₁)
        (inverseImageUnder (J := J) (K := K) F f) ≫ comparisonInv (J := J) (K := K) F f =
      (ringPullback (J := J) (K := K) F).map
        (FreeAlgebra.Presentation.base O₁ (Under.mk f)) ∧
    comparisonInv (J := J) (K := K) F f ≫ (ringPullback (J := J) (K := K) F).map
        (FreeAlgebra.Presentation.map O₁ (Under.mk f)) =
      FreeAlgebra.Presentation.map
        ((ringPullback (J := J) (K := K) F).obj O₁)
        (inverseImageUnder (J := J) (K := K) F f) := sorry

/-- The polynomial comparison followed by its reverse is the identity. -/
theorem comparison_hom_inv_id [RepresentablyFlat F] (f : O₁ ⟶ O₂) :
    comparison (J := J) (K := K) F f ≫ comparisonInv (J := J) (K := K) F f = 𝟙 _ := sorry

/-- The reverse polynomial comparison followed by the comparison is the identity. -/
theorem comparison_inv_hom_id [RepresentablyFlat F] (f : O₁ ⟶ O₂) :
    comparisonInv (J := J) (K := K) F f ≫ comparison (J := J) (K := K) F f = 𝟙 _ := sorry

/-- A representably flat inverse image identifies the two canonical polynomial presentations. -/
instance comparison_isIso [RepresentablyFlat F] (f : O₁ ⟶ O₂) :
    IsIso (comparison (J := J) (K := K) F f) :=
  ⟨⟨comparisonInv (J := J) (K := K) F f, comparison_hom_inv_id (J := J) (K := K) F f, comparison_inv_hom_id (J := J) (K := K) F f⟩⟩

/-- Transposing the presentation comparison recovers its explicit adjoint-side map. -/
@[simp]
theorem comparison_adj (f : O₁ ⟶ O₂) :
    (F.sheafAdjunctionContinuous CommRingCat.{u} J K).homEquiv _ _
        (comparison (J := J) (K := K) F f) =
      adjoint (J := J) (K := K) F f :=
  Equiv.apply_symm_apply _ _

end InverseImage
end Presentation
end NaiveCotangent
end RingedSite
end SheafOfModules
