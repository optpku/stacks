module

public import Mathlib.CategoryTheory.Functor.ReflectsIso.Jointly
public import ReasLib.CategoryTheory.Sites.Point.SheafifiedRepresentable

/-!
# Point fibers and separating sections

This module gives the point-fiber API used to turn equality of germs into
refinements and to package section-separating families of points as jointly
isomorphism-reflecting stalk functors.
-/

@[expose] public section

open CategoryTheory Opposite
open CategoryTheory.Limits

universe w v u w' w''

namespace CategoryTheory.GrothendieckTopology.Point

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

/-- A family of point stalk functors jointly reflects isomorphisms when its germs separate
unequal sections of every large type-valued sheaf. -/
lemma stalkFamily_jointlyReflectsIsomorphisms_of_separatingSections
    {ι : Type w} (p : ι → GrothendieckTopology.Point.{w'} J)
    (hsep :
      ∀ ⦃ℱ : Sheaf J (Type (max u v w'))⦄ (U : C) (s s' : ℱ.obj.obj (op U)),
        s ≠ s' →
          ∃ i : ι, ∃ x : (p i).fiber.obj U,
            (p i).toPresheafFiber U x ℱ.obj s ≠ (p i).toPresheafFiber U x ℱ.obj s') :
    JointlyReflectIsomorphisms
      (fun i : ι ↦ ((p i).sheafFiber :
        Sheaf J (Type (max u v w')) ⥤ Type (max u v w'))) := sorry

/-- Equality of two germs in a point fiber is witnessed after restricting both sections to a
common refinement of the chosen point element. -/
lemma germEq_iff_existsRefinement
    (q : GrothendieckTopology.Point.{w'} J) {P : Cᵒᵖ ⥤ Type w''}
    [Limits.HasColimitsOfSize.{w', w'} (Type w'')]
    (X : C) (x : q.fiber.obj X) (z₁ z₂ : P.obj (op X)) :
    q.toPresheafFiber X x P z₁ = q.toPresheafFiber X x P z₂ ↔
      ∃ (Y : C) (f : Y ⟶ X) (y : q.fiber.obj Y),
        q.fiber.map f y = x ∧ P.map f.op z₁ = P.map f.op z₂ := sorry

/-- Equality of two germs of sections supplies a lift of the point element through their
equalizer sieve. -/
lemma germEq_gives_equalizerLift
    (q : GrothendieckTopology.Point.{w'} J) {ℱ : Sheaf J (Type (max u v w'))} (U : C)
    (s s' : ℱ.obj.obj (op U)) {x : q.fiber.obj U}
    (h : q.toPresheafFiber U x ℱ.obj s = q.toPresheafFiber U x ℱ.obj s') :
    ∃ (Y : C) (g : Y ⟶ U) (_ : Presheaf.equalizerSieve (F := ℱ.obj) s s' g)
      (y : q.fiber.obj Y), q.fiber.map g y = x := sorry

/-- A small type-valued sheaf viewed in the larger point-fiber universe by `ULift`. -/
abbrev uliftSheaf (ℱ : Sheaf J (Type w')) : Sheaf J (Type (max u v w')) :=
  (sheafCompose J
    (CategoryTheory.uliftFunctor.{max u v, w'} : Type w' ⥤ Type (max u v w'))).obj ℱ

/-- Equality of lifted germs is equivalent to equality of the original germs before applying
`ULift`. -/
lemma uliftGerm_eq_iff
    (q : GrothendieckTopology.Point.{w'} J) {ℱ : Sheaf J (Type w')} (U : C)
    (x : q.fiber.obj U) (s s' : ℱ.obj.obj (op U)) :
    q.toPresheafFiber U x (uliftSheaf.{v, u, w'} ℱ).obj (ULift.up s) =
      q.toPresheafFiber U x (uliftSheaf.{v, u, w'} ℱ).obj (ULift.up s') ↔
      q.toPresheafFiber U x ℱ.obj s = q.toPresheafFiber U x ℱ.obj s' := sorry

end CategoryTheory.GrothendieckTopology.Point
