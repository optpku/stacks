/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Topology.Category.TopCat.Limits.Basic
public import Mathlib.Topology.Sheaves.SheafOfFunctions
public import ReasLib.CategoryTheory.Functor.Algebraic.Basic
public import ReasLib.Topology.Category.TopCat.Concrete

/-!
# Pointwise product presheaves

This file constructs the `C`-valued presheaf whose sections over an open `U` are the categorical
product of a family `A : X → C` over the points of `U`. For a category of algebraic structures,
its underlying type-valued presheaf is the usual dependent-function sheaf.

## API under `TopCat.Presheaf.PointwiseProduct`

- `presheaf A` — the product presheaf
- `forgetComponentIso` — identifies underlying type with dependent functions
- `forgetIso` — identifies underlying presheaf with `presheafToTypes`
- `isSheaf` — the product presheaf is a sheaf
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

noncomputable section

universe u v w

namespace TopCat.Presheaf.PointwiseProduct

section Core

variable {X : TopCat.{u}} {C : Type v} [Category.{w} C] [HasProducts.{u} C]

/-- Reindexing along the identity is the identity. -/
theorem restriction_id (A : X → C) (U : (Opens X)ᵒᵖ) :
    Pi.map' (𝟙 U).unop (fun _ ↦ 𝟙 _) = 𝟙 (∏ᶜ fun x : U.unop ↦ A x.1) := sorry

/-- Reindexing along a composite is the composite of reindexings. -/
theorem restriction_comp (A : X → C)
    {U V W : (Opens X)ᵒᵖ} (i : U ⟶ V) (j : V ⟶ W) :
    (Pi.map' (i ≫ j).unop (fun x : W.unop ↦ 𝟙 (A x.1)) :
        (∏ᶜ fun x : U.unop ↦ A x.1) ⟶ ∏ᶜ fun x : W.unop ↦ A x.1) =
      (Pi.map' i.unop (fun x : V.unop ↦ 𝟙 (A x.1)) :
          (∏ᶜ fun x : U.unop ↦ A x.1) ⟶ ∏ᶜ fun x : V.unop ↦ A x.1) ≫
        (Pi.map' j.unop (fun x : W.unop ↦ 𝟙 (A x.1)) :
          (∏ᶜ fun x : V.unop ↦ A x.1) ⟶ ∏ᶜ fun x : W.unop ↦ A x.1) := sorry

/-- The `C`-valued presheaf whose sections over `U` are `∏ₓ∈U A(x)`. -/
def presheaf (A : X → C) : X.Presheaf C where
  obj U := ∏ᶜ fun x : U.unop ↦ A x.1
  map {_ _} i := Pi.map' i.unop (fun _ ↦ 𝟙 _)
  map_id U := restriction_id A U
  map_comp i j := restriction_comp A i j

end Core

section Forget

variable {X : TopCat.{w}} {C : Type v} [Category.{w} C]
variable (F : C ⥤ Type w) [IsAlgebraicStructure C F]

/-- The underlying set of sections is the dependent function type. -/
def forgetComponentIso (A : X → C) (U : (Opens X)ᵒᵖ) :
    F.obj ((presheaf A).obj U) ≅ (∀ x : U.unop, F.obj (A x.1)) :=
  PreservesProduct.iso F (fun x : U.unop ↦ A x.1) ≪≫ Types.productIso _

/-- The product comparison is natural with respect to restriction. -/
theorem forgetComponentIso_naturality (A : X → C)
    {U V : (Opens X)ᵒᵖ} (i : U ⟶ V) :
    (presheaf A ⋙ F).map i ≫ (forgetComponentIso F A V).hom =
      (forgetComponentIso F A U).hom ≫
        (presheafToTypes X (fun x ↦ F.obj (A x))).map i := sorry

/-- Applying the forgetful functor gives the dependent-function presheaf. -/
def forgetIso (A : X → C) :
    presheaf A ⋙ F ≅ presheafToTypes X (fun x ↦ F.obj (A x)) :=
  NatIso.ofComponents
    (fun U ↦ forgetComponentIso F A U)
    (fun {_ _} i ↦ forgetComponentIso_naturality F A i)

/-- The pointwise product presheaf is a sheaf. -/
@[stacks 007R "pointwise product presheaf is a sheaf"]
theorem isSheaf (A : X → C) : (presheaf A).IsSheaf := sorry

end Forget

section TopCat

variable {X : TopCat.{u}}

/-- A pointwise product of topological spaces is a sheaf of topological spaces.

Unlike `isSheaf`, this specialization does not use a forgetful functor to detect the sheaf
condition: `TopCat ⥤ Type` does not reflect isomorphisms. -/
theorem isSheaf_topCat (A : X → TopCat.{max u v}) :
    (presheaf A).IsSheaf := sorry

end TopCat

end TopCat.Presheaf.PointwiseProduct

end

end
