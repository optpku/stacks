module

public import ReasLib.CategoryTheory.Pro.Sequential.Presentation

/-!
# Realization of sequential representatives as pro-morphisms

This leaf sends an explicit monotone representative to the canonical morphism between the
associated pro-objects and records its identity and composition computations.
-/

@[expose] public section

open CategoryTheory Limits Opposite

noncomputable section

universe u v

namespace CategoryTheory.Pro.SequentialHom

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

variable {C : Type u} [Category.{v} C] {X Y : ℕᵒᵖ ⥤ C}

/-- The class in `colim_m Hom(X_m, Y_n)` represented by the level map at `n`. -/
private noncomputable def classAt (r : Pro.SequentialHom X Y) (n : ℕ) :
    (colimit (X.op ⋙ yoneda)).obj (op (op (Y.obj (op n)))) :=
  (colimit.ι (X.op ⋙ yoneda) (op (op (r.reindex n)))).app
    (op (op (Y.obj (op n)))) (r.hom.app (op n)).op

/-- The Hom-colimit classes of a representative are compatible with transitions in the target. -/
private theorem classAtNaturality (r : Pro.SequentialHom X Y)
    {i j : ℕᵒᵖ} (f : i ⟶ j) :
    (colimit (X.op ⋙ yoneda)).map (Y.map f).op.op (r.classAt i.unop) =
      r.classAt j.unop := sorry

/-- The compatible inverse-limit point determined by a sequential representative. -/
private noncomputable def toLimit (r : Pro.SequentialHom X Y) :
    limit (Y.op.op ⋙ colimit (X.op ⋙ yoneda)) :=
  Types.Limit.mk _ (fun i ↦ r.classAt i.unop.unop.unop)
    (fun _ _ f ↦ r.classAtNaturality f.unop.unop)

/-- The morphism between the associated pro-objects determined by a sequential representative. -/
noncomputable def toHom (r : Pro.SequentialHom X Y) :
    (Pro.lim (C := C) ℕᵒᵖ).obj X ⟶ (Pro.lim (C := C) ℕᵒᵖ).obj Y :=
  (Pro.limHomEquiv X Y).symm r.toLimit

/-- The identity sequential representative realizes as the identity pro-morphism. -/
theorem toHom_id (X : ℕᵒᵖ ⥤ C) :
    (id X).toHom = 𝟙 ((Pro.lim (C := C) ℕᵒᵖ).obj X) := sorry

/-- Composition of sequential representatives realizes as composition of pro-morphisms. -/
theorem toHom_comp {Z : ℕᵒᵖ ⥤ C} (r : Pro.SequentialHom X Y)
    (s : Pro.SequentialHom Y Z) :
    (comp r s).toHom = r.toHom ≫ s.toHom := sorry

end CategoryTheory.Pro.SequentialHom
