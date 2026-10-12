/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module
public import ReasLib.CategoryTheory.MorphismProperty.Representable.ChangeOfBase

@[expose] public section
open CategoryTheory CategoryTheory.Limits
noncomputable section
universe u v

namespace CategoryTheory.Functor.relativelyRepresentable.ChangeOfSource
variable {C : Type u} [Category.{v} C]
variable {F F' G : Cᵒᵖ ⥤ Type v} (f : F ⟶ G) (f' : F' ⟶ G)
variable (hf : yoneda.relativelyRepresentable f) (hf' : yoneda.relativelyRepresentable f')
variable (α : F ⟶ F') [IsIso α] (h : α ≫ f' = f)
variable {A : C} (a : yoneda.obj A ⟶ G)
include h

theorem compatibility : (hf.fst a ≫ α) ≫ f' = yoneda.map (hf.snd a) ≫ a := by
  rw [Category.assoc, h]
  exact hf.w a

def map : hf.pullback a ⟶ hf'.pullback a :=
  hf'.lift (hf.fst a ≫ α) (hf.snd a) (compatibility f f' hf α h a)

set_option backward.isDefEq.respectTransparency false in
theorem isPullback : IsPullback (map f f' hf hf' α h a) (hf.snd a) (hf'.snd a) (𝟙 A) := by
  have outer : IsPullback (hf.fst a ≫ α) (yoneda.map (hf.snd a)) f' a := by
    have square : IsPullback α f f' (𝟙 G) := IsPullback.of_horiz_isIso ⟨by simpa using h⟩
    simpa only [Category.comp_id] using (hf.isPullback a).paste_horiz square
  apply IsPullback.of_map yoneda
    ((hf'.lift_snd (hf.fst a ≫ α) (hf.snd a) (compatibility f f' hf α h a)).trans
      (Category.comp_id _).symm)
  rw [yoneda.map_id]
  have w : (hf.fst a ≫ α) ≫ f' = (yoneda.map (hf.snd a) ≫ 𝟙 _) ≫ a := by
    simpa using outer.w
  have outer' : IsPullback (hf.fst a ≫ α) (yoneda.map (hf.snd a)) f' (𝟙 _ ≫ a) := by
    simpa only [Category.id_comp] using outer
  simpa only [map, Functor.relativelyRepresentable.lift, Functor.map_preimage,
    Functor.map_id, IsPullback.lift, Category.comp_id] using
      IsPullback.of_right' outer' (hf'.isPullback a)

end CategoryTheory.Functor.relativelyRepresentable.ChangeOfSource
