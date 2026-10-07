module

public import ReasLib.Algebra.Category.ModuleCat.Presheaf.CommRing
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Monoidal
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Bilinear maps of presheaves of modules

A restriction-compatible family of bilinear maps between module presheaves is canonically
equivalent to a morphism from their pointwise tensor product.  This is the site-independent
owner of the bilinear universal property used by module sheaves and geometric specializations.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.MonoidalCategory

noncomputable section

universe u v w

namespace PresheafOfModules

variable {C : Type u} [Category.{v} C]
variable (R : Cᵒᵖ ⥤ CommRingCat.{w})

/-- A family of bilinear maps on sections which commutes with every restriction map. -/
@[stacks 03L6 "bilinear maps of module presheaves"]
structure BilinearMap
    (F G H : PresheafOfModules.{w} (ringPresheaf R)) where
  /-- The bilinear map over an object of the indexing category. -/
  app (U : Cᵒᵖ) :
    F.obj U →ₗ[R.obj U] G.obj U →ₗ[R.obj U] H.obj U
  /-- The objectwise bilinear maps commute with restriction. -/
  naturality {U V : Cᵒᵖ} (i : U ⟶ V) (x : F.obj U) (y : G.obj U) :
    H.map i (app U x y) = app V (F.map i x) (G.map i y)

namespace BilinearMap

variable {R}
variable {F G H : PresheafOfModules.{w} (ringPresheaf R)}

/-- Two compatible bilinear maps are equal when they agree on every pair of sections. -/
@[ext]
theorem ext {b c : BilinearMap R F G H}
    (h : ∀ (U : Cᵒᵖ) (x : F.obj U) (y : G.obj U), b.app U x y = c.app U x y) :
    b = c := sorry

/-- The objectwise tensor-product morphism represented by a compatible bilinear map. -/
noncomputable def toHomApp (b : BilinearMap R F G H) (U : Cᵒᵖ) :
    (Monoidal.tensorObj F G).obj U ⟶ H.obj U :=
  ModuleCat.ofHom (TensorProduct.lift (b.app U))

/-- The objectwise tensor lifts of a compatible bilinear map commute with restriction. -/
theorem toHomApp_naturality (b : BilinearMap R F G H)
    {U V : Cᵒᵖ} (i : U ⟶ V) :
    (Monoidal.tensorObj F G).map i ≫
        (ModuleCat.restrictScalars (R.map i).hom).map (b.toHomApp V) =
      b.toHomApp U ≫ H.map i := sorry

/-- The tensor-product morphism represented by a compatible bilinear map. -/
@[stacks 03L6 "tensor morphism represented by a bilinear map"]
noncomputable def toHom (b : BilinearMap R F G H) :
    Monoidal.tensorObj F G ⟶ H where
  app U := b.toHomApp U
  naturality := b.toHomApp_naturality

/-- Evaluation of the represented tensor morphism on a pure tensor. -/
@[simp]
theorem toHom_tmul (b : BilinearMap R F G H) (U : Cᵒᵖ)
    (x : F.obj U) (y : G.obj U) :
    (b.toHom.app U).hom (x ⊗ₜ[R.obj U] y) = b.app U x y := sorry

/-- The objectwise bilinear map obtained by evaluating a tensor morphism on pure tensors. -/
noncomputable def ofHomApp (f : Monoidal.tensorObj F G ⟶ H) (U : Cᵒᵖ) :
    F.obj U →ₗ[R.obj U] G.obj U →ₗ[R.obj U] H.obj U :=
  (TensorProduct.mk (R.obj U) (F.obj U) (G.obj U)).compr₂ (f.app U).hom

/-- Evaluation on pure tensors commutes with restriction for every tensor morphism. -/
theorem ofHomApp_naturality (f : Monoidal.tensorObj F G ⟶ H)
    {U V : Cᵒᵖ} (i : U ⟶ V) (x : F.obj U) (y : G.obj U) :
    H.map i (ofHomApp f U x y) =
      ofHomApp f V (F.map i x) (G.map i y) := sorry

/-- The compatible bilinear map obtained from a tensor-product morphism. -/
noncomputable def ofHom (f : Monoidal.tensorObj F G ⟶ H) :
    BilinearMap R F G H where
  app U := ofHomApp f U
  naturality := ofHomApp_naturality f

/-- The bilinear map recovered from a tensor morphism is evaluation on pure tensors. -/
@[simp]
theorem ofHom_app (f : Monoidal.tensorObj F G ⟶ H) (U : Cᵒᵖ)
    (x : F.obj U) (y : G.obj U) :
    (ofHom f).app U x y = (f.app U).hom (x ⊗ₜ[R.obj U] y) := sorry

/-- Converting a compatible bilinear map to a tensor morphism and back is the identity. -/
@[simp]
theorem ofHom_toHom (b : BilinearMap R F G H) :
    ofHom b.toHom = b := sorry

/-- Converting a tensor morphism to a compatible bilinear map and back is the identity. -/
@[simp]
theorem toHom_ofHom (f : Monoidal.tensorObj F G ⟶ H) :
    (ofHom f).toHom = f := sorry

/-- Compatible bilinear maps are canonically equivalent to morphisms from the tensor product. -/
@[stacks 03L6 "bilinear universal property for module presheaves"]
noncomputable def homEquiv :
    BilinearMap R F G H ≃ (Monoidal.tensorObj F G ⟶ H) where
  toFun := toHom
  invFun := ofHom
  left_inv := ofHom_toHom
  right_inv := toHom_ofHom

/-- Transport a compatible bilinear map contravariantly in its inputs and covariantly in its
target. -/
noncomputable def map
    {F' G' H' : PresheafOfModules.{w} (ringPresheaf R)}
    (b : BilinearMap R F G H) (f : F' ⟶ F) (g : G' ⟶ G) (h : H ⟶ H') :
    BilinearMap R F' G' H' :=
  ofHom ((f ⊗ₘ g) ≫ b.toHom ≫ h)

/-- Transported bilinear maps act by precomposition on both inputs and postcomposition on the
target. -/
@[simp]
theorem map_app
    {F' G' H' : PresheafOfModules.{w} (ringPresheaf R)}
    (b : BilinearMap R F G H) (f : F' ⟶ F) (g : G' ⟶ G) (h : H ⟶ H')
    (U : Cᵒᵖ) (x : F'.obj U) (y : G'.obj U) :
    (b.map f g h).app U x y = (h.app U).hom (b.app U ((f.app U).hom x) ((g.app U).hom y)) :=
  sorry

/-- Under the universal-property equivalence, transport is composition with tensor morphisms. -/
theorem toHom_map
    {F' G' H' : PresheafOfModules.{w} (ringPresheaf R)}
    (b : BilinearMap R F G H) (f : F' ⟶ F) (g : G' ⟶ G) (h : H ⟶ H') :
    (b.map f g h).toHom = (f ⊗ₘ g) ≫ b.toHom ≫ h := sorry

end BilinearMap

end PresheafOfModules


