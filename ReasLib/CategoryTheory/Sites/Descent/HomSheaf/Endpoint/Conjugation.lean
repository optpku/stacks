module

public import ReasLib.CategoryTheory.Sites.Descent.HomPresheaf.Endpoint.Conjugation

/-!
# Endpoint isomorphisms for canonical Hom-sheaves

For a prestack, the canonical Hom-presheaves are sheaves. This leaf lifts the
endpoint-conjugation isomorphism of Hom-presheaves through the fully faithful
inclusion of sheaves into presheaves. The construction is deliberately owned
by `Pseudofunctor.sheafHom`: it applies to every `Cat`-valued prestack and does
not depend on a chosen fibered-category presentation.
-/

@[expose] public section

universe uC vC uP vP

namespace CategoryTheory

open Opposite
open scoped CategoryTheory.Bicategory

namespace Pseudofunctor

variable {C : Type uC} [Category.{vC} C]

/-- Conjugation by isomorphisms of both endpoint objects, as an isomorphism of canonical
Hom-sheaves. -/
noncomputable def SheafHom.Congr.iso
    (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{vP, uP})
    (J : GrothendieckTopology C) [F.IsPrestack J]
    {U : C} {x₁ x₂ y₁ y₂ : F.obj (.mk (op U))}
    (ex : x₁ ≅ x₂) (ey : y₁ ≅ y₂) :
    F.sheafHom J x₁ y₁ ≅ F.sheafHom J x₂ y₂ :=
  (fullyFaithfulSheafToPresheaf (J.over U) (Type vP)).preimageIso
    (Pseudofunctor.PresheafHom.Congr.iso F ex ey)

/-- The forward morphism of `SheafHom.Congr.iso` is the endpoint-conjugation morphism of
the underlying Hom-presheaves. -/
@[simp]
theorem SheafHom.Congr.Iso.hom
    (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{vP, uP})
    (J : GrothendieckTopology C) [F.IsPrestack J]
    {U : C} {x₁ x₂ y₁ y₂ : F.obj (.mk (op U))}
    (ex : x₁ ≅ x₂) (ey : y₁ ≅ y₂) :
    (SheafHom.Congr.iso F J ex ey).hom.hom =
      (Pseudofunctor.PresheafHom.Congr.iso F ex ey).hom := sorry

/-- The inverse morphism of `SheafHom.Congr.iso` is the inverse endpoint-conjugation morphism
of the underlying Hom-presheaves. -/
@[simp]
theorem SheafHom.Congr.Iso.inv
    (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{vP, uP})
    (J : GrothendieckTopology C) [F.IsPrestack J]
    {U : C} {x₁ x₂ y₁ y₂ : F.obj (.mk (op U))}
    (ex : x₁ ≅ x₂) (ey : y₁ ≅ y₂) :
    (SheafHom.Congr.iso F J ex ey).inv.hom =
      (Pseudofunctor.PresheafHom.Congr.iso F ex ey).inv := sorry

/-- Evaluation of the forward Hom-sheaf endpoint-conjugation map is the corresponding
Hom-presheaf component. -/
@[simp]
theorem SheafHom.Congr.Iso.Hom.app
    (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{vP, uP})
    (J : GrothendieckTopology C) [F.IsPrestack J]
    {U : C} {x₁ x₂ y₁ y₂ : F.obj (.mk (op U))}
    (ex : x₁ ≅ x₂) (ey : y₁ ≅ y₂) (W : (Over U)ᵒᵖ) :
    (SheafHom.Congr.iso F J ex ey).hom.hom.app W =
      (Pseudofunctor.PresheafHom.Congr.iso F ex ey).hom.app W := sorry

/-- Evaluation of the inverse Hom-sheaf endpoint-conjugation map is the inverse
Hom-presheaf component. -/
@[simp]
theorem SheafHom.Congr.Iso.Inv.app
    (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{vP, uP})
    (J : GrothendieckTopology C) [F.IsPrestack J]
    {U : C} {x₁ x₂ y₁ y₂ : F.obj (.mk (op U))}
    (ex : x₁ ≅ x₂) (ey : y₁ ≅ y₂) (W : (Over U)ᵒᵖ) :
    (SheafHom.Congr.iso F J ex ey).inv.hom.app W =
      (Pseudofunctor.PresheafHom.Congr.iso F ex ey).inv.app W := sorry

/-- Elementwise computation of the forward Hom-sheaf endpoint-conjugation map. -/
@[simp]
theorem SheafHom.Congr.Iso.Hom.appApply
    (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{vP, uP})
    (J : GrothendieckTopology C) [F.IsPrestack J]
    {U : C} {x₁ x₂ y₁ y₂ : F.obj (.mk (op U))}
    (ex : x₁ ≅ x₂) (ey : y₁ ≅ y₂) (W : (Over U)ᵒᵖ)
    (φ : (F.presheafHom x₁ y₁).obj W) :
    (SheafHom.Congr.iso F J ex ey).hom.hom.app W φ =
      Iso.homCongr
        ((F.map W.unop.hom.op.toLoc).toFunctor.mapIso ex)
        ((F.map W.unop.hom.op.toLoc).toFunctor.mapIso ey) φ := sorry

/-- Elementwise computation of the inverse Hom-sheaf endpoint-conjugation map. -/
@[simp]
theorem SheafHom.Congr.Iso.Inv.appApply
    (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{vP, uP})
    (J : GrothendieckTopology C) [F.IsPrestack J]
    {U : C} {x₁ x₂ y₁ y₂ : F.obj (.mk (op U))}
    (ex : x₁ ≅ x₂) (ey : y₁ ≅ y₂) (W : (Over U)ᵒᵖ)
    (φ : (F.presheafHom x₂ y₂).obj W) :
    (SheafHom.Congr.iso F J ex ey).inv.hom.app W φ =
      Iso.homCongr
        ((F.map W.unop.hom.op.toLoc).toFunctor.mapIso ex.symm)
        ((F.map W.unop.hom.op.toLoc).toFunctor.mapIso ey.symm) φ := sorry

/-- At the identity slice, forward Hom-sheaf endpoint conjugation is ordinary conjugation. -/
@[simp]
theorem SheafHom.Congr.Iso.Hom.identitySlice
    (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{vP, uP})
    (J : GrothendieckTopology C) [F.IsPrestack J]
    {U : C} {x₁ x₂ y₁ y₂ : F.obj (.mk (op U))}
    (ex : x₁ ≅ x₂) (ey : y₁ ≅ y₂) (φ : x₁ ⟶ y₁) :
    (SheafHom.Congr.iso F J ex ey).hom.hom.app (op (Over.mk (𝟙 U)))
        (F.presheafHomObjHomEquiv φ) =
      F.presheafHomObjHomEquiv (ex.inv ≫ φ ≫ ey.hom) := sorry

/-- At the identity slice, inverse Hom-sheaf endpoint conjugation is inverse conjugation. -/
@[simp]
theorem SheafHom.Congr.Iso.Inv.identitySlice
    (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{vP, uP})
    (J : GrothendieckTopology C) [F.IsPrestack J]
    {U : C} {x₁ x₂ y₁ y₂ : F.obj (.mk (op U))}
    (ex : x₁ ≅ x₂) (ey : y₁ ≅ y₂) (φ : x₂ ⟶ y₂) :
    (SheafHom.Congr.iso F J ex ey).inv.hom.app (op (Over.mk (𝟙 U)))
        (F.presheafHomObjHomEquiv φ) =
      F.presheafHomObjHomEquiv (ex.hom ≫ φ ≫ ey.inv) := sorry

/-- Conjugation by identity endpoint isomorphisms is the identity Hom-sheaf isomorphism. -/
@[simp]
theorem SheafHom.Congr.Iso.refl
    (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{vP, uP})
    (J : GrothendieckTopology C) [F.IsPrestack J]
    {U : C} (x y : F.obj (.mk (op U))) :
    SheafHom.Congr.iso F J (Iso.refl x) (Iso.refl y) =
      Iso.refl (F.sheafHom J x y) := sorry

/-- Reversing both endpoint isomorphisms reverses the Hom-sheaf isomorphism. -/
@[simp]
theorem SheafHom.Congr.Iso.symm
    (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{vP, uP})
    (J : GrothendieckTopology C) [F.IsPrestack J]
    {U : C} {x₁ x₂ y₁ y₂ : F.obj (.mk (op U))}
    (ex : x₁ ≅ x₂) (ey : y₁ ≅ y₂) :
    (SheafHom.Congr.iso F J ex ey).symm =
      SheafHom.Congr.iso F J ex.symm ey.symm := sorry

/-- Endpoint-conjugation isomorphisms of Hom-sheaves compose along endpoint isomorphisms. -/
theorem SheafHom.Congr.Iso.trans
    (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{vP, uP})
    (J : GrothendieckTopology C) [F.IsPrestack J]
    {U : C} {x₁ x₂ x₃ y₁ y₂ y₃ : F.obj (.mk (op U))}
    (ex₁₂ : x₁ ≅ x₂) (ex₂₃ : x₂ ≅ x₃)
    (ey₁₂ : y₁ ≅ y₂) (ey₂₃ : y₂ ≅ y₃) :
    SheafHom.Congr.iso F J ex₁₂ ey₁₂ ≪≫
        SheafHom.Congr.iso F J ex₂₃ ey₂₃ =
      SheafHom.Congr.iso F J (ex₁₂ ≪≫ ex₂₃) (ey₁₂ ≪≫ ey₂₃) := sorry

end Pseudofunctor

end CategoryTheory
