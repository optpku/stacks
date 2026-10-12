/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module
public import Mathlib.CategoryTheory.MorphismProperty.Representable
public import Mathlib.CategoryTheory.Limits.Preserves.Yoneda

@[expose] public section
open CategoryTheory CategoryTheory.Limits
noncomputable section
universe u v

namespace CategoryTheory.Functor.relativelyRepresentable.ChangeOfBase
variable {C : Type u} [Category.{v} C]
variable {F G : Cᵒᵖ ⥤ Type v} {f : F ⟶ G} (hf : yoneda.relativelyRepresentable f)
variable {A B : C} (a : yoneda.obj A ⟶ G) (b : yoneda.obj B ⟶ G)
variable (t : A ⟶ B) (h : yoneda.map t ≫ b = a)

include h

/-- The commutativity needed for the actual represented-fibre lift. -/
theorem compatibility :
    hf.fst a ≫ f = yoneda.map (hf.snd a ≫ t) ≫ b := by
  rw [Functor.map_comp, Category.assoc, h]
  exact hf.w a

/-- The actual morphism between represented fibres. -/
def map : hf.pullback a ⟶ hf.pullback b :=
  hf.lift (hf.fst a) (hf.snd a ≫ t) (compatibility hf a b t h)

/-- Its square over the base map commutes. -/
theorem map_snd : map hf a b t h ≫ hf.snd b = hf.snd a ≫ t :=
  hf.lift_snd (hf.fst a) (hf.snd a ≫ t) (compatibility hf a b t h)

set_option backward.isDefEq.respectTransparency false in
/-- The represented change-of-base square is cartesian, with a complete proof. -/
theorem isPullback : IsPullback (map hf a b t h) (hf.snd a) (hf.snd b) t := by
  apply IsPullback.of_map yoneda (map_snd hf a b t h)
  have outer : IsPullback (hf.fst a) (yoneda.map (hf.snd a)) f (yoneda.map t ≫ b) := by
    rw [h]
    exact hf.isPullback a
  simpa only [map, Functor.relativelyRepresentable.lift, Functor.map_preimage, IsPullback.lift,
    Functor.map_comp] using IsPullback.of_right' outer (hf.isPullback b)

end CategoryTheory.Functor.relativelyRepresentable.ChangeOfBase
