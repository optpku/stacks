/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.PseudoPullback.Projections
import Mathlib.Tactic.CrossRefAttribute

/-!
# Graph into an identity pseudo-pullback: construction

For a based functor `F : X ⥤ᵇ Y`, this leaf constructs the canonical graph
`X ⥤ᵇ BasedCategory.PseudoPullback F (𝟭 Y)` and records its objectwise,
morphismwise, and projection computations. The graph unit, counit, and equivalence data are
provided by the subsequent `Graph.Unit`, `Graph.Counit`, and `Graph.Equivalence` modules.
-/

@[expose] public section

universe u v uX vX uY vY

namespace CategoryTheory
namespace BasedCategory.PseudoPullback

open Functor.Fiber
open scoped BasedFunctor

variable {C : Type u} [Category.{v} C]
variable {X : BasedCategory.{vX, uX} C}
variable {Y : BasedCategory.{vY, uY} C}

noncomputable section

section GraphImplementation

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace Implementation

/-- The source object lies in the fibre over its own image in the base. -/
private theorem graphFstObj_mem (x : X.obj) :
    X.p.obj x = X.p.obj x := sorry
/- Proof strategy: reflexivity. This named statement supplies the proof field of the explicit
fibre object without placing a proof script inside its data constructor. -/

/-- The object `(X.p.obj x, x, F.obj x, 𝟙 (F.obj x))` of the identity pseudo-pullback. -/
private def graphObj (F : X ⥤ᵇ Y) (x : X.obj) :
    (PseudoPullback F (𝟭 Y)).obj :=
  mk F (𝟭 Y) (X.p.obj x)
    { fst := ⟨x, graphFstObj_mem x⟩
      snd := ⟨F.obj x, F.w_obj x⟩
      iso := Iso.refl _ }

/-- The component pair `(a, F.map a)` respects the identity comparisons. -/
private theorem graphMap_comm (F : X ⥤ᵇ Y) {x y : X.obj} (a : x ⟶ y) :
    CommSq (F.map a) (𝟙 (F.obj x)) (𝟙 (F.obj y)) (F.map a) := sorry
/- Proof strategy: unfold `CommSq`; functoriality of the identity functor and the unit laws reduce
both sides to `F.map a`. -/

/-- The pseudo-pullback morphism with components `(a, F.map a)`. -/
private def graphMap (F : X ⥤ᵇ Y) {x y : X.obj} (a : x ⟶ y) :
    graphObj F x ⟶ graphObj F y :=
  PseudoPullback.Hom.mk (X.p.map a) a
    (Functor.IsHomLift.map a) (F.map a)
    (BasedFunctor.preserves_isHomLift F (X.p.map a) a)
    (graphMap_comm F a)

/-- The graph assignment preserves identity morphisms. -/
private theorem graphMap_id (F : X ⥤ᵇ Y) (x : X.obj) :
    graphMap F (𝟙 x) = 𝟙 (graphObj F x) := sorry
/- Proof strategy: apply `PseudoPullback.hom_ext`; the components are the identity-map equations
for `X.p` and `F.toFunctor`. -/

/-- The graph assignment preserves composition. -/
private theorem graphMap_comp (F : X ⥤ᵇ Y) {x y z : X.obj}
    (a : x ⟶ y) (b : y ⟶ z) :
    graphMap F (a ≫ b) = graphMap F a ≫ graphMap F b := sorry
/- Proof strategy: apply `PseudoPullback.hom_ext`; the components are the composition-map
equations for `X.p` and `F.toFunctor`. -/

/-- The total-category functor underlying the graph. -/
private def graphFunctor (F : X ⥤ᵇ Y) :
    X.obj ⥤ (PseudoPullback F (𝟭 Y)).obj where
  obj := graphObj F
  map := graphMap F
  map_id := graphMap_id F
  map_comp := graphMap_comp F

/-- The graph functor preserves the common base projection. -/
private theorem graphFunctor_comm (F : X ⥤ᵇ Y) :
    graphFunctor F ⋙ (PseudoPullback F (𝟭 Y)).p = X.p := sorry
/- Proof strategy: use functor extensionality; `graphObj` stores `X.p.obj x` and `graphMap` stores
`X.p.map a` as their base components. -/

end Implementation

/-- The canonical graph from a based category into the pseudo-pullback of `F` and `𝟭 Y`. -/
@[stacks 0040 "graph into an explicit pseudo-pullback with an identity leg"]
def graph (F : X ⥤ᵇ Y) : X ⥤ᵇ PseudoPullback F (𝟭 Y) where
  toFunctor := Implementation.graphFunctor F
  w := Implementation.graphFunctor_comm F

end GraphImplementation

/-- The graph retains the source object's base object. -/
@[simp]
theorem graph.obj.base (F : X ⥤ᵇ Y) (x : X.obj) :
    baseObj ((graph F).obj x) = X.p.obj x := sorry
/- Proof strategy: unfold `graph`, its explicit object constructor, and `baseObj`. -/

/-- The first component of a graph object is the original object. -/
@[simp]
theorem graph.obj.fst (F : X ⥤ᵇ Y) (x : X.obj) :
    fstObj ((graph F).obj x) = x := sorry
/- Proof strategy: unfold `graph`, its explicit object constructor, and `fstObj`. -/

/-- The second component of a graph object is its image under `F`. -/
@[simp]
theorem graph.obj.snd (F : X ⥤ᵇ Y) (x : X.obj) :
    sndObj ((graph F).obj x) = F.obj x := sorry
/- Proof strategy: unfold `graph`, its explicit object constructor, and `sndObj`. -/

/-- The comparison carried by a graph object is the identity of its image under `F`. -/
@[simp]
theorem graph.obj.comparison (F : X ⥤ᵇ Y) (x : X.obj) :
    comparison ((graph F).obj x) = 𝟙 (F.obj x) := sorry
/- Proof strategy: unfold `graph`, its explicit object constructor, and `comparison`. -/

/-- The objectwise comparison isomorphism of a graph object is the identity isomorphism. -/
@[simp]
theorem graph.obj.comparisonIso (F : X ⥤ᵇ Y) (x : X.obj) :
    comparisonIsoApp ((graph F).obj x) =
      Iso.refl (F.obj x) := sorry

/-- The common base component of a graph morphism is its image under the source projection. -/
@[simp]
theorem graph.map.base (F : X ⥤ᵇ Y) {x y : X.obj} (a : x ⟶ y) :
    baseMap ((graph F).map a) = X.p.map a := sorry
/- Proof strategy: unfold `graph`, its explicit morphism constructor, and `baseMap`. -/

/-- The first component of a graph morphism is the original morphism. -/
@[simp]
theorem graph.map.fst (F : X ⥤ᵇ Y) {x y : X.obj} (a : x ⟶ y) :
    fstMap ((graph F).map a) = a := sorry
/- Proof strategy: unfold `graph`, its explicit morphism constructor, and `fstMap`. -/

/-- The second component of a graph morphism is its image under `F`. -/
@[simp]
theorem graph.map.snd (F : X ⥤ᵇ Y) {x y : X.obj} (a : x ⟶ y) :
    sndMap ((graph F).map a) = F.map a := sorry
/- Proof strategy: unfold `graph`, its explicit morphism constructor, and `sndMap`. -/

/-- The first projection of the graph is the identity based functor. -/
@[simp]
theorem graph.fst (F : X ⥤ᵇ Y) :
    graph F ⋙ fst F (𝟭 Y) = 𝟭 X := sorry
/- Proof strategy: apply based-functor extensionality and use `graph.obj.fst` and
`graph.map.fst`. -/

/-- The second projection of the graph is the original based functor. -/
@[simp]
theorem graph.snd (F : X ⥤ᵇ Y) :
    graph F ⋙ snd F (𝟭 Y) = F := sorry
/- Proof strategy: apply based-functor extensionality and use `graph.obj.snd` and
`graph.map.snd`. -/

end

end BasedCategory.PseudoPullback
end CategoryTheory
