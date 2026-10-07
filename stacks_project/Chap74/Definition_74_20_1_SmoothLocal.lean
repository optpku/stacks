module

public import Mathlib.CategoryTheory.CommSq
public import Mathlib.CategoryTheory.MorphismProperty.Limits
public import stacks_project.Chap65.Lemma_65_7_3_Pullback
public import stacks_project.Chap67.Lemma_67_37_4_Smooth

/-!
# Smooth locality on source-and-target

A morphism property of algebraic spaces over a scheme `S` is smooth local on
source-and-target when it is stable under smooth precomposition and smooth base
change, and can be checked on pointwise commutative squares with smooth vertical
arrows.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

universe u

noncomputable section

namespace AlgebraicGeometry.AlgebraicSpace

/-- There is a commutative square over `f` through `x` with smooth vertical arrows
whose top arrow satisfies `P`. -/
def existsSmoothSquareAt {S : Scheme.{u}} (P : MorphismProperty (AlgebraicSpace S))
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) (x : Points X) : Prop :=
  ∃ (U V : AlgebraicSpace S) (a : U ⟶ X) (b : V ⟶ Y) (h : U ⟶ V) (u : Points U),
    Smooth a ∧ Smooth b ∧ Points.map a u = x ∧ CommSq h a b f ∧ P h

/-- `existsSmoothSquareAt P f x` is the existence of a commutative square over `f`
through `x` with smooth vertical arrows on which `P` holds. -/
theorem existsSmoothSquareAt_def {S : Scheme.{u}}
    (P : MorphismProperty (AlgebraicSpace S)) {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) (x : Points X) :
    existsSmoothSquareAt P f x ↔
      ∃ (U V : AlgebraicSpace S) (a : U ⟶ X) (b : V ⟶ Y) (h : U ⟶ V) (u : Points U),
        Smooth a ∧ Smooth b ∧ Points.map a u = x ∧ CommSq h a b f ∧ P h :=
  Iff.rfl

namespace existsSmoothSquareAt

/-- A commutative square with smooth vertical arrows through `x` on which `P`
holds witnesses `existsSmoothSquareAt P f x`. -/
theorem of {S : Scheme.{u}} {P : MorphismProperty (AlgebraicSpace S)}
    {X Y : AlgebraicSpace S} {f : X ⟶ Y} {x : Points X} {U V : AlgebraicSpace S}
    (a : U ⟶ X) (b : V ⟶ Y) (h : U ⟶ V) (u : Points U)
    (ha : Smooth a) (hb : Smooth b) (hx : Points.map a u = x)
    (sq : CommSq h a b f) (hP : P h) : existsSmoothSquareAt P f x :=
  sorry

/-- A witness of `existsSmoothSquareAt P f x` supplies a commutative square over
`f` through `x` with smooth vertical arrows on which `P` holds. -/
theorem spec {S : Scheme.{u}} {P : MorphismProperty (AlgebraicSpace S)}
    {X Y : AlgebraicSpace S} {f : X ⟶ Y} {x : Points X}
    (h : existsSmoothSquareAt P f x) :
    ∃ (U V : AlgebraicSpace S) (a : U ⟶ X) (b : V ⟶ Y) (h : U ⟶ V) (u : Points U),
      Smooth a ∧ Smooth b ∧ Points.map a u = x ∧ CommSq h a b f ∧ P h :=
  sorry

end existsSmoothSquareAt

/-- A morphism property of algebraic spaces over `S` is smooth local on
source-and-target when it is stable under smooth precomposition and smooth base
change, and can be checked on pointwise smooth squares. -/
class IsSmoothLocalAtSourceAndTarget {S : Scheme.{u}}
    (P : MorphismProperty (AlgebraicSpace S)) : Prop where
  /-- The property is preserved by precomposition with a smooth morphism. -/
  respectsLeftSmooth : P.RespectsLeft (@Smooth S : MorphismProperty (AlgebraicSpace S))
  /-- The property is preserved by base change along a smooth morphism. -/
  stableUnderSmoothBaseChange :
    P.IsStableUnderBaseChangeAgainst (@Smooth S : MorphismProperty (AlgebraicSpace S))
  /-- The property holds exactly when it holds after passing to a commutative
  square with smooth vertical morphisms through every source point. -/
  locality {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    P f ↔ ∀ x : Points X, existsSmoothSquareAt P f x

namespace IsSmoothLocalAtSourceAndTarget

variable {S : Scheme.{u}} (P : MorphismProperty (AlgebraicSpace S))

/-- A smooth-local-on-source-and-target property respects smooth precomposition. -/
instance toRespectsLeftSmooth [hP : IsSmoothLocalAtSourceAndTarget P] :
    P.RespectsLeft (@Smooth S : MorphismProperty (AlgebraicSpace S)) :=
  hP.respectsLeftSmooth

/-- A smooth-local-on-source-and-target property is stable under smooth base change. -/
instance toStableUnderSmoothBaseChange [hP : IsSmoothLocalAtSourceAndTarget P] :
    P.IsStableUnderBaseChangeAgainst (@Smooth S : MorphismProperty (AlgebraicSpace S)) :=
  hP.stableUnderSmoothBaseChange

/-- The pointwise smooth-square characterization of a property that is smooth
local on source-and-target. -/
theorem iff_exists [IsSmoothLocalAtSourceAndTarget P] {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) : P f ↔ ∀ x : Points X, existsSmoothSquareAt P f x :=
  sorry

/-- A smooth-local-on-source-and-target property is stable under smooth
precomposition, stable under the base-change projection `pullback.snd f g`,
and characterized by pointwise smooth squares. -/
theorem spec [IsSmoothLocalAtSourceAndTarget P] :
    (∀ {X Y Z : AlgebraicSpace S} (f : X ⟶ Y) (g : Y ⟶ Z),
      Smooth f → P g → P (f ≫ g)) ∧
    (∀ {X Y Y' : AlgebraicSpace S} (f : X ⟶ Y) (g : Y' ⟶ Y),
      Smooth g → P f → P (pullback.snd f g)) ∧
    (∀ {X Y : AlgebraicSpace S} (f : X ⟶ Y),
      P f ↔ ∀ x : Points X, existsSmoothSquareAt P f x) :=
  sorry

/-- A smooth-local-on-source-and-target property is preserved by precomposition
with a smooth morphism. -/
theorem precomp [IsSmoothLocalAtSourceAndTarget P] {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (g : Y ⟶ Z) (hf : Smooth f) (hg : P g) : P (f ≫ g) :=
  sorry

/-- A smooth-local-on-source-and-target property is preserved by the base-change
projection `pullback.snd f g` along a smooth morphism. -/
theorem pullback_snd [IsSmoothLocalAtSourceAndTarget P]
    {X Y Y' : AlgebraicSpace S} (f : X ⟶ Y) (g : Y' ⟶ Y)
    (hg : Smooth g) (hf : P f) : P (pullback.snd f g) :=
  sorry

end IsSmoothLocalAtSourceAndTarget

end AlgebraicGeometry.AlgebraicSpace
