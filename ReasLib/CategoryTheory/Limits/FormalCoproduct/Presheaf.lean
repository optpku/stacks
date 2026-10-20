module

public import Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Products
public import Mathlib.CategoryTheory.Limits.Types.Coproducts
public import ReasLib.CategoryTheory.Limits.FormalCoproduct.Map
import Mathlib.Tactic.CrossRefAttribute

/-!
# Representable presheaves of formal coproducts

This module evaluates the Yoneda embedding on a formal coproduct and records the resulting
pointwise sigma presentation.  It is independent of any site topology.
-/

@[expose] public section

universe w v u

namespace CategoryTheory

open Opposite

namespace Limits
namespace FormalCoproduct

variable {C : Type u} [Category.{v} C]

/-- Evaluating the lifted Yoneda embedding on a formal coproduct produces the coproduct of the
presheaves represented by its members. -/
@[stacks 01G1 "presheaf associated to a formal coproduct"]
noncomputable def toPresheaf :
    FormalCoproduct.{w} C ⥤ (Cᵒᵖ ⥤ Type (max w v)) :=
  (FormalCoproduct.eval C (Cᵒᵖ ⥤ Type (max w v))).obj (uliftYoneda.{w})

/-- The lifted sigma presentation of sections of the presheaf associated to a formal coproduct. -/
noncomputable def toPresheafObjIsoULift (K : FormalCoproduct.{w} C) (X : Cᵒᵖ) :
    (toPresheaf.obj K).obj X ≅ Σ i : K.I, ULift.{w} (X.unop ⟶ K.obj i) :=
  (sigmaObjIso (fun i : K.I ↦ uliftYoneda.obj (K.obj i)) X) ≪≫
    Types.coproductIso (fun i : K.I ↦ ULift.{w} (X.unop ⟶ K.obj i))

/-- The summand of `toPresheaf.obj K` determined by an index and a section into that component.
-/
noncomputable def toPresheafObjMk (K : FormalCoproduct.{w} C) (X : Cᵒᵖ)
    (i : K.I) (g : X.unop ⟶ K.obj i) :
    (toPresheaf.obj K).obj X :=
  ((Sigma.ι (fun j : K.I ↦ uliftYoneda.obj (K.obj j)) i).app X) (ULift.up g)

/-- Sections of the presheaf of a formal coproduct are pairs of an index and a section into the
corresponding component. -/
noncomputable def toPresheafObjEquiv (K : FormalCoproduct.{w} C) (X : Cᵒᵖ) :
    (toPresheaf.obj K).obj X ≃ Σ i : K.I, X.unop ⟶ K.obj i :=
  (toPresheafObjIsoULift K X).toEquiv.trans (Equiv.sigmaCongrRight fun _ ↦ Equiv.ulift)

/-- The sigma presentation sends the canonical coproduct summand to its supplied index and
section. -/
@[simp] theorem toPresheafObjEquiv_ι (K : FormalCoproduct.{w} C) (X : Cᵒᵖ)
    (i : K.I) (g : X.unop ⟶ K.obj i) :
    K.toPresheafObjEquiv X (K.toPresheafObjMk X i g) = ⟨i, g⟩ := sorry

/-- The inverse sigma presentation sends a supplied index and section to the canonical coproduct
summand. -/
@[simp] theorem toPresheafObjEquiv_symm_sigma (K : FormalCoproduct.{w} C) (X : Cᵒᵖ)
    (i : K.I) (g : X.unop ⟶ K.obj i) :
    (K.toPresheafObjEquiv X).symm ⟨i, g⟩ = K.toPresheafObjMk X i g := sorry

/-- The presheaf map induced by a formal-coproduct morphism sends a canonical summand by the
component map and its reindexing function. -/
@[simp] theorem toPresheaf_map_objMk {K L : FormalCoproduct.{w} C} (φ : K ⟶ L) (X : Cᵒᵖ)
    (i : K.I) (g : X.unop ⟶ K.obj i) :
    ((toPresheaf.map φ).app X) (K.toPresheafObjMk X i g) =
      L.toPresheafObjMk X (φ.f i) (g ≫ φ.φ i) := sorry

end FormalCoproduct
end Limits
end CategoryTheory
