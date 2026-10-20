module

public import ReasLib.CategoryTheory.Sites.LocallyConstant.Basic
public import Mathlib.CategoryTheory.Sites.Point.Over

/-!
# Constant charts containing a site point

The chart is selected from the local constant models supplied by the caller. The point's
cover-surjectivity field gives an actual lift into one of the covering chart objects.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

noncomputable section
universe w v u a b

namespace CategoryTheory.Sheaf

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [LocallySmall.{w} C] (Φ : GrothendieckTopology.Point.{w} J)
variable {D : Type a} [Category.{b} D]
variable [HasWeakSheafify J D] [∀ U : C, HasWeakSheafify (J.over U) D]
variable (P : D → Prop) (F : Sheaf J D)

/-- A supplied constant model on a neighborhood containing the specified site point. -/
structure PointedConstantChart where
  U : C
  point : Φ.fiber.obj U
  model : D
  property : P model
  iso : F.over U ≅ (constantSheaf (J.over U) D).obj model

/-- Select a genuine pointed chart from the local constant models in the given instance. -/
def pointedConstantChart [IsLocallyConstantWith P F] : PointedConstantChart Φ P F := by
  classical
  let N : Φ.fiber.Elements := Classical.choice (IsCofiltered.nonempty (C := Φ.fiber.Elements))
  let h := IsLocallyConstantWith.existsConstantCover (P := P) (F := F) N.1
  let I := h.choose
  let X : I → Over N.1 := h.choose_spec.choose
  have hcover : (J.over N.1).CoversTop X := h.choose_spec.choose_spec.1
  let Ψ := Φ.over N.2
  let T : Over N.1 := Over.mk (𝟙 N.1)
  let p : Ψ.fiber.obj T := ⟨N.2, by sorry⟩
  let lift := Ψ.jointly_surjective (Sieve.ofObjects X T) (hcover T) p
  let V := lift.choose
  let q : V ⟶ T := lift.choose_spec.choose
  have hq : Sieve.ofObjects X T q := lift.choose_spec.choose_spec.choose
  let j : I := hq.choose
  let g : V ⟶ X j := hq.choose_spec.some
  let v : Ψ.fiber.obj V := lift.choose_spec.choose_spec.choose_spec.choose
  let x : Ψ.fiber.obj (X j) := Ψ.fiber.map g v
  let model := (h.choose_spec.choose_spec.2 j).choose
  exact
    { U := (X j).left
      point := x.val
      model := model
      property := (h.choose_spec.choose_spec.2 j).choose_spec.1
      iso := (h.choose_spec.choose_spec.2 j).choose_spec.2.some }

end CategoryTheory.Sheaf
