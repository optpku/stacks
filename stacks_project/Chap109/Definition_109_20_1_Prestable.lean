/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.CategoryTheory.ObjectProperty.Basic
public import stacks_project.Chap65.Lemma_65_7_3_Pullback
public import stacks_project.Chap70.Lemma_70_14_4_Pullback
public import stacks_project.Chap76.Definition_76_55_1_AtWorstNodal
public import stacks_project.Chap99.Situation_99_15_1_Category

/-!
# Prestable morphisms of algebraic spaces

A morphism of algebraic spaces is prestable when it is at-worst-nodal of
relative dimension 1 and the unit `𝒪_Y ⟶ f_* 𝒪_X` remains an isomorphism
after every base change.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
open CategoryTheory.ObjectProperty

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- A morphism `f : X ⟶ Y` of algebraic spaces is prestable if it is
at-worst-nodal of relative dimension 1 and the unit `𝒪_Y ⟶ f_* 𝒪_X` is an
isomorphism after every base change. -/
@[mk_iff]
class Prestable {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) : Prop
    extends AtWorstNodal f where
  /-- The unit `𝒪_Z ⟶ (f ×_Y Z)_* 𝒪_{X ×_Y Z}` is an isomorphism for every
  base change `g : Z ⟶ Y`. -/
  universallyUnitToPushforwardObjUnit_isIso :
    ∀ {Z : AlgebraicSpace S} (g : Z ⟶ Y),
      IsIso (Modules.unitToPushforwardObjUnit (pullback.snd f g))

namespace Prestable

/-- A prestable morphism is at-worst-nodal of relative dimension 1. -/
instance instAtWorstNodal {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [h : Prestable f] : AtWorstNodal f :=
  h.toAtWorstNodal

/-- A prestable morphism is at-worst-nodal of relative dimension 1, and the
unit `𝒪_Y ⟶ f_* 𝒪_X` is an isomorphism after every base change. -/
theorem spec {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [Prestable f] :
    AtWorstNodal f ∧
      ∀ {Z : AlgebraicSpace S} (g : Z ⟶ Y),
        IsIso (Modules.unitToPushforwardObjUnit (pullback.snd f g)) :=
  sorry

end Prestable

/-- A proper geometrically connected at-worst-nodal morphism of schemes over
`S` is prestable as a morphism of algebraic spaces. -/
instance instPrestable_ofOverMap {S : Scheme.{u}} {U V : Over S} (h : U ⟶ V)
    [AlgebraicGeometry.AtWorstNodal h.left] [IsProper h.left]
    [GeometricallyConnected h.left] : Prestable (ofOverMap h) :=
  sorry

/-- The second projection of a pullback of a prestable morphism is prestable. -/
instance instPrestable_pullback_snd {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (g : Z ⟶ Y) [Prestable f] : Prestable (pullback.snd f g) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace

namespace AlgebraicGeometry.AlgebraicSpace.Spaces.Curves

/-- The object property of prestable families of curves. -/
def prestable (S : Scheme.{u}) : ObjectProperty (Obj S) :=
  fun P ↦ Prestable (hom P)

/-- Membership in `prestable` is prestability of the structure morphism. -/
theorem prestable_iff {S : Scheme.{u}} (P : Obj S) :
    prestable S P ↔ Prestable (hom P) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Spaces.Curves
