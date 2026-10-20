module

public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.CategoryTheory.ObjectProperty.Basic
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Curve.Prestable
public import stacks_project.Chap65.Lemma_65_7_3_Pullback
public import stacks_project.Chap70.Lemma_70_14_4_Pullback
public import stacks_project.Chap76.Definition_76_55_1_AtWorstNodal
public import stacks_project.Chap99.Situation_99_15_1_Category

/-!
# Prestable morphisms of algebraic spaces

A family of curves is prestable when it is at-worst-nodal of relative
dimension 1 and the canonical unit `𝒪_Y ⟶ f_* 𝒪_X` remains an isomorphism
after every base change.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
open CategoryTheory.ObjectProperty

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/- Prestability of a morphism of algebraic spaces. -/
#check (AlgebraicGeometry.AlgebraicSpace.Prestable :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S}, (X ⟶ Y) → Prop)

#check (AlgebraicGeometry.AlgebraicSpace.Prestable.spec :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Prestable f],
    Spaces.Curves.IsFamily f ∧ AtWorstNodal f ∧
      ∀ {Z : AlgebraicSpace S} (g : Z ⟶ Y),
        IsIso (Modules.unitToPushforwardObjUnit (pullback.snd f g)))

#check (AlgebraicGeometry.AlgebraicSpace.instPrestable_ofOverMap :
  ∀ {S : Scheme.{u}} {U V : Over S} (h : U ⟶ V)
    [AlgebraicGeometry.AtWorstNodal h.left] [IsProper h.left]
    [GeometricallyConnected h.left], Prestable (ofOverMap h))

#check (AlgebraicGeometry.AlgebraicSpace.instPrestable_pullback_snd :
  ∀ {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (g : Z ⟶ Y) [Prestable f], Prestable (pullback.snd f g))

end AlgebraicGeometry.AlgebraicSpace

namespace AlgebraicGeometry.AlgebraicSpace.Spaces.Curves

#check (AlgebraicGeometry.AlgebraicSpace.Spaces.Curves.prestable :
  ∀ S : Scheme.{u}, ObjectProperty (Obj S))

#check (AlgebraicGeometry.AlgebraicSpace.Spaces.Curves.prestable_iff :
  ∀ {S : Scheme.{u}} (P : Obj S), prestable S P ↔ Prestable (hom P))

end AlgebraicGeometry.AlgebraicSpace.Spaces.Curves
