/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.Presheaf.InverseImage

/-!
# Natural isomorphisms acting on presheaf inverse image

Opposite whiskering sends a natural isomorphism of covariant functors to a
contravariant isomorphism of their presheaf inverse-image functors.
-/

@[expose] public section

open CategoryTheory Opposite

universe u v u' v' w

namespace CategoryTheory.Functor

variable {C : Type u} [Category.{v} C]
variable {D : Type u'} [Category.{v'} D]

/-- The isomorphism of `A`-valued presheaf inverse images induced by a natural
isomorphism of covariant functors. If `e : F ≅ G`, then this is
`presheafInverseImage G A ≅ presheafInverseImage F A`. -/
def presheafInverseImageIso {F G : C ⥤ D} (e : F ≅ G) (A : Type w) [Category A] :
    presheafInverseImage G A ≅ presheafInverseImage F A :=
  (whiskeringLeft Cᵒᵖ Dᵒᵖ A).mapIso (NatIso.op e)

/-- The component of `presheafInverseImageIso e A` at a presheaf `𝒢` and an
object `x` is `𝒢.map (e.hom.app x).op`. -/
theorem presheafInverseImageIso_hom_app {F G : C ⥤ D} (e : F ≅ G)
    (A : Type w) [Category A] (𝒢 : Dᵒᵖ ⥤ A) (x : C) :
    ((presheafInverseImageIso e A).hom.app 𝒢).app (op x) =
      𝒢.map (e.hom.app x).op :=
  sorry

/-- The inverse-image isomorphism assigned to an identity natural isomorphism is
the identity. -/
theorem presheafInverseImageIso_refl (F : C ⥤ D) (A : Type w) [Category A] :
    presheafInverseImageIso (Iso.refl F) A = Iso.refl (presheafInverseImage F A) :=
  sorry

/-- Opposite whiskering reverses the order of composition of natural
isomorphisms. -/
theorem presheafInverseImageIso_trans {F G H : C ⥤ D} (e : F ≅ G) (d : G ≅ H)
    (A : Type w) [Category A] :
    presheafInverseImageIso (e ≪≫ d) A =
      presheafInverseImageIso d A ≪≫ presheafInverseImageIso e A :=
  sorry

end CategoryTheory.Functor
