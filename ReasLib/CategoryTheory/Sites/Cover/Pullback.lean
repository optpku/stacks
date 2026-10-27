/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.Cover.Basic
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Transport between pullback covers in a slice

For a fixed cover of `U`, an arrow in the pullback cover above `V : C / U`
can be transported covariantly along a morphism `V ⟶ W` in the slice.  This
is the concrete indexing API behind restriction of coverwise descent data.
-/

@[expose] public section

universe u v

namespace CategoryTheory.GrothendieckTopology.Cover

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C} {U : C}

namespace Arrow

/-- The postcomposed arrow belongs to the pullback cover above the target of a slice morphism. -/
theorem mapOver_mem (T : J.Cover U) {V W : Over U} (g : V ⟶ W)
    (I : (T.pullback V.hom).Arrow) :
    (T.pullback W.hom) (I.f ≫ g.left) := by
  change T ((I.f ≫ g.left) ≫ W.hom)
  simpa only [Category.assoc, Over.w] using (coe_pullback V.hom I.f T).mp I.hf

/-- Transport an arrow of a pullback cover along a morphism in the slice over the original
cover target. -/
def mapOver (T : J.Cover U) {V W : Over U} (g : V ⟶ W)
    (I : (T.pullback V.hom).Arrow) :
    (T.pullback W.hom).Arrow :=
  ⟨I.Y, I.f ≫ g.left, mapOver_mem T g I⟩

/-- The structure map of a transported pullback-cover arrow is postcomposition by the slice
morphism. -/
@[simp]
theorem mapOver_f (T : J.Cover U) {V W : Over U} (g : V ⟶ W)
    (I : (T.pullback V.hom).Arrow) :
    (mapOver T g I).f = I.f ≫ g.left := rfl

/-- Transporting a pullback-cover arrow preserves its underlying arrow in the original cover. -/
@[simp]
theorem mapOver_base (T : J.Cover U) {V W : Over U} (g : V ⟶ W)
    (I : (T.pullback V.hom).Arrow) :
    (mapOver T g I).base = I.base := by
  cases I
  simp [mapOver, base, Category.assoc]

/-- Transport along an identity slice morphism does not change a pullback-cover arrow. -/
@[simp]
theorem mapOver_id (T : J.Cover U) (V : Over U)
    (I : (T.pullback V.hom).Arrow) :
    mapOver T (𝟙 V) I = I := by
  cases I
  simp [mapOver]

/-- Transport of pullback-cover arrows respects composition in the slice. -/
@[simp]
theorem mapOver_comp (T : J.Cover U) {V W X : Over U} (g : V ⟶ W) (h : W ⟶ X)
    (I : (T.pullback V.hom).Arrow) :
    mapOver T h (mapOver T g I) = mapOver T (g ≫ h) I := by
  cases I
  simp [mapOver, Category.assoc]

end Arrow

namespace Relation

/-- The relation witnesses remain compatible after transporting both arrows along a slice
morphism. -/
theorem mapOver_w (T : J.Cover U) {V W : Over U} (g : V ⟶ W)
    (R : (T.pullback V.hom).Relation) :
    R.r.g₁ ≫ (Arrow.mapOver T g R.fst).f =
      R.r.g₂ ≫ (Arrow.mapOver T g R.snd).f := by
  simpa only [Arrow.mapOver_f] using R.r.w_assoc g.left

/-- Transport a relation of a pullback cover along a morphism in the slice. -/
def mapOver (T : J.Cover U) {V W : Over U} (g : V ⟶ W)
    (R : (T.pullback V.hom).Relation) :
    (T.pullback W.hom).Relation :=
  Relation.mk'
    (fst := Arrow.mapOver T g R.fst)
    (snd := Arrow.mapOver T g R.snd)
    { Z := R.r.Z
      g₁ := R.r.g₁
      g₂ := R.r.g₂
      w := mapOver_w T g R }

/-- The first endpoint of a transported relation is the transport of its first endpoint. -/
@[simp]
theorem mapOver_fst (T : J.Cover U) {V W : Over U} (g : V ⟶ W)
    (R : (T.pullback V.hom).Relation) :
    (mapOver T g R).fst = Arrow.mapOver T g R.fst := rfl

/-- The second endpoint of a transported relation is the transport of its second endpoint. -/
@[simp]
theorem mapOver_snd (T : J.Cover U) {V W : Over U} (g : V ⟶ W)
    (R : (T.pullback V.hom).Relation) :
    (mapOver T g R).snd = Arrow.mapOver T g R.snd := rfl

/-- Transport along an identity slice morphism does not change a pullback-cover relation. -/
@[simp]
theorem mapOver_id (T : J.Cover U) (V : Over U)
    (R : (T.pullback V.hom).Relation) :
    mapOver T (𝟙 V) R = R := by
  rcases R with @⟨⟨Y₁, f₁, hf₁⟩, ⟨Y₂, f₂, hf₂⟩, ⟨Z, g₁, g₂, w⟩⟩
  simp only [mapOver, mk', Arrow.mapOver, Over.id_left, mk.injEq, Category.comp_id,
    true_and]
  congr 1
  · simp
  · simp
  · exact proof_irrel_heq _ _

/-- Transport of pullback-cover relations respects composition in the slice. -/
@[simp]
theorem mapOver_comp (T : J.Cover U) {V W X : Over U} (g : V ⟶ W) (h : W ⟶ X)
    (R : (T.pullback V.hom).Relation) :
    mapOver T h (mapOver T g R) = mapOver T (g ≫ h) R := by
  rcases R with @⟨⟨Y₁, f₁, hf₁⟩, ⟨Y₂, f₂, hf₂⟩, ⟨Z, g₁, g₂, w⟩⟩
  simp only [mapOver, mk', Arrow.mapOver, Over.comp_left, mk.injEq, Category.assoc,
    true_and]
  congr 1
  · simp [Category.assoc]
  · simp [Category.assoc]
  · exact proof_irrel_heq _ _

end Relation

end CategoryTheory.GrothendieckTopology.Cover
