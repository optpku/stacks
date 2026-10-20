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
    (T.pullback W.hom) (I.f ≫ g.left) := sorry

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
    (mapOver T g I).f = I.f ≫ g.left := sorry

/-- Transporting a pullback-cover arrow preserves its underlying arrow in the original cover. -/
@[simp]
theorem mapOver_base (T : J.Cover U) {V W : Over U} (g : V ⟶ W)
    (I : (T.pullback V.hom).Arrow) :
    (mapOver T g I).base = I.base := sorry

/-- Transport along an identity slice morphism does not change a pullback-cover arrow. -/
@[simp]
theorem mapOver_id (T : J.Cover U) (V : Over U)
    (I : (T.pullback V.hom).Arrow) :
    mapOver T (𝟙 V) I = I := sorry

/-- Transport of pullback-cover arrows respects composition in the slice. -/
@[simp]
theorem mapOver_comp (T : J.Cover U) {V W X : Over U} (g : V ⟶ W) (h : W ⟶ X)
    (I : (T.pullback V.hom).Arrow) :
    mapOver T h (mapOver T g I) = mapOver T (g ≫ h) I := sorry

end Arrow

namespace Relation

/-- The relation witnesses remain compatible after transporting both arrows along a slice
morphism. -/
theorem mapOver_w (T : J.Cover U) {V W : Over U} (g : V ⟶ W)
    (R : (T.pullback V.hom).Relation) :
    R.r.g₁ ≫ (Arrow.mapOver T g R.fst).f =
      R.r.g₂ ≫ (Arrow.mapOver T g R.snd).f := sorry

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
    (mapOver T g R).fst = Arrow.mapOver T g R.fst := sorry

/-- The second endpoint of a transported relation is the transport of its second endpoint. -/
@[simp]
theorem mapOver_snd (T : J.Cover U) {V W : Over U} (g : V ⟶ W)
    (R : (T.pullback V.hom).Relation) :
    (mapOver T g R).snd = Arrow.mapOver T g R.snd := sorry

/-- Transport along an identity slice morphism does not change a pullback-cover relation. -/
@[simp]
theorem mapOver_id (T : J.Cover U) (V : Over U)
    (R : (T.pullback V.hom).Relation) :
    mapOver T (𝟙 V) R = R := sorry

/-- Transport of pullback-cover relations respects composition in the slice. -/
@[simp]
theorem mapOver_comp (T : J.Cover U) {V W X : Over U} (g : V ⟶ W) (h : W ⟶ X)
    (R : (T.pullback V.hom).Relation) :
    mapOver T h (mapOver T g R) = mapOver T (g ≫ h) R := sorry

end Relation

end CategoryTheory.GrothendieckTopology.Cover
