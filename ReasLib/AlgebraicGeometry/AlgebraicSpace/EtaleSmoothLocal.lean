/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.CommSq
public import Mathlib.CategoryTheory.MorphismProperty.Limits
public import Mathlib.CategoryTheory.MorphismProperty.Local
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtalePrecoverage
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.LocalAtTarget.BaseChange
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Surjective
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Pullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Etale
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Smooth
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points

/-!
# Étale-smooth locality on source-and-target

A morphism property of algebraic spaces over a scheme `S` is étale-smooth local
on source-and-target when it is stable under étale precomposition and smooth
base change, and can be checked on pointwise commutative squares with a smooth
right vertical arrow and étale comparison into the fibre product.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

universe u

noncomputable section

namespace AlgebraicGeometry.AlgebraicSpace

/-- The comparison morphism `U ⟶ X ×_Y V` induced by a commutative square over
`f` with top arrow `h` and vertical arrows `a`, `b`. -/
def etaleSmoothSquareLift {S : Scheme.{u}} {X Y U V : AlgebraicSpace S}
    {f : X ⟶ Y} {a : U ⟶ X} {b : V ⟶ Y} {h : U ⟶ V}
    (sq : CommSq h a b f) : U ⟶ pullback f b :=
  pullback.lift a h sq.w.symm

/-- The comparison `etaleSmoothSquareLift sq` recovers the left vertical arrow
`a` after composing with `pullback.fst`. -/
theorem etaleSmoothSquareLift_fst {S : Scheme.{u}} {X Y U V : AlgebraicSpace S}
    {f : X ⟶ Y} {a : U ⟶ X} {b : V ⟶ Y} {h : U ⟶ V}
    (sq : CommSq h a b f) :
    etaleSmoothSquareLift sq ≫ pullback.fst f b = a :=
  sorry

/-- The comparison `etaleSmoothSquareLift sq` recovers the top arrow `h` after
composing with `pullback.snd`. -/
theorem etaleSmoothSquareLift_snd {S : Scheme.{u}} {X Y U V : AlgebraicSpace S}
    {f : X ⟶ Y} {a : U ⟶ X} {b : V ⟶ Y} {h : U ⟶ V}
    (sq : CommSq h a b f) :
    etaleSmoothSquareLift sq ≫ pullback.snd f b = h :=
  sorry

/-- There is a commutative square over `f` through `x` with smooth right vertical
arrow, étale comparison into the fibre product, and top arrow satisfying `P`. -/
def existsEtaleSmoothSquareAt {S : Scheme.{u}} (P : MorphismProperty (AlgebraicSpace S))
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) (x : Points X) : Prop :=
  ∃ (U V : AlgebraicSpace S) (a : U ⟶ X) (b : V ⟶ Y) (h : U ⟶ V) (u : Points U)
    (sq : CommSq h a b f),
      Smooth b ∧ Etale (etaleSmoothSquareLift sq) ∧ Points.map a u = x ∧ P h

/-- `existsEtaleSmoothSquareAt P f x` is the existence of a commutative square
over `f` through `x` with smooth right vertical arrow and étale comparison on
which `P` holds. -/
theorem existsEtaleSmoothSquareAt_def {S : Scheme.{u}}
    (P : MorphismProperty (AlgebraicSpace S)) {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) (x : Points X) :
    existsEtaleSmoothSquareAt P f x ↔
      ∃ (U V : AlgebraicSpace S) (a : U ⟶ X) (b : V ⟶ Y) (h : U ⟶ V) (u : Points U)
        (sq : CommSq h a b f),
          Smooth b ∧ Etale (etaleSmoothSquareLift sq) ∧ Points.map a u = x ∧ P h :=
  Iff.rfl

namespace existsEtaleSmoothSquareAt

/-- A commutative square with smooth right vertical arrow, étale comparison, and
top arrow of `P` through `x` witnesses `existsEtaleSmoothSquareAt P f x`. -/
theorem of {S : Scheme.{u}} {P : MorphismProperty (AlgebraicSpace S)}
    {X Y : AlgebraicSpace S} {f : X ⟶ Y} {x : Points X} {U V : AlgebraicSpace S}
    (a : U ⟶ X) (b : V ⟶ Y) (h : U ⟶ V) (u : Points U)
    (sq : CommSq h a b f) (hb : Smooth b) (hcomp : Etale (etaleSmoothSquareLift sq))
    (hx : Points.map a u = x) (hP : P h) : existsEtaleSmoothSquareAt P f x :=
  sorry

/-- A witness of `existsEtaleSmoothSquareAt P f x` supplies a commutative square
over `f` through `x` with smooth right vertical arrow, étale comparison, and top
arrow of `P`. -/
theorem spec {S : Scheme.{u}} {P : MorphismProperty (AlgebraicSpace S)}
    {X Y : AlgebraicSpace S} {f : X ⟶ Y} {x : Points X}
    (h : existsEtaleSmoothSquareAt P f x) :
    ∃ (U V : AlgebraicSpace S) (a : U ⟶ X) (b : V ⟶ Y) (h : U ⟶ V) (u : Points U)
      (sq : CommSq h a b f),
        Smooth b ∧ Etale (etaleSmoothSquareLift sq) ∧ Points.map a u = x ∧ P h :=
  sorry

end existsEtaleSmoothSquareAt

/-- A morphism property of algebraic spaces over `S` is étale-smooth local on
source-and-target when it is stable under étale precomposition and smooth base
change, and can be checked on pointwise mixed étale-smooth squares. -/
class IsEtaleSmoothLocalAtSourceAndTarget {S : Scheme.{u}}
    (P : MorphismProperty (AlgebraicSpace S)) : Prop where
  /-- The property is preserved by precomposition with an étale morphism. -/
  respectsLeftEtale : P.RespectsLeft (@Etale S : MorphismProperty (AlgebraicSpace S))
  /-- The property is preserved by base change along a smooth morphism. -/
  stableUnderSmoothBaseChange :
    P.IsStableUnderBaseChangeAgainst (@Smooth S : MorphismProperty (AlgebraicSpace S))
  /-- The property holds exactly when it holds after passing to a commutative
  square with smooth right vertical morphism and étale comparison through every
  source point. -/
  locality {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    P f ↔ ∀ x : Points X, existsEtaleSmoothSquareAt P f x

namespace IsEtaleSmoothLocalAtSourceAndTarget

variable {S : Scheme.{u}} (P : MorphismProperty (AlgebraicSpace S))

/-- An étale-smooth-local-on-source-and-target property respects étale
precomposition. -/
instance toRespectsLeftEtale [hP : IsEtaleSmoothLocalAtSourceAndTarget P] :
    P.RespectsLeft (@Etale S : MorphismProperty (AlgebraicSpace S)) :=
  hP.respectsLeftEtale

/-- An étale-smooth-local-on-source-and-target property is stable under smooth
base change. -/
instance toStableUnderSmoothBaseChange [hP : IsEtaleSmoothLocalAtSourceAndTarget P] :
    P.IsStableUnderBaseChangeAgainst (@Smooth S : MorphismProperty (AlgebraicSpace S)) :=
  hP.stableUnderSmoothBaseChange

/-- The pointwise mixed-square characterization of a property that is
étale-smooth local on source-and-target. -/
theorem iff_exists [IsEtaleSmoothLocalAtSourceAndTarget P] {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) : P f ↔ ∀ x : Points X, existsEtaleSmoothSquareAt P f x :=
  sorry

/-- An étale-smooth-local-on-source-and-target property is stable under étale
precomposition, stable under the base-change projection `pullback.snd f g`
along a smooth morphism, and characterized by pointwise mixed squares. -/
theorem spec [IsEtaleSmoothLocalAtSourceAndTarget P] :
    (∀ {X Y Z : AlgebraicSpace S} (f : X ⟶ Y) (g : Y ⟶ Z),
      Etale f → P g → P (f ≫ g)) ∧
    (∀ {X Y Y' : AlgebraicSpace S} (f : X ⟶ Y) (g : Y' ⟶ Y),
      Smooth g → P f → P (pullback.snd f g)) ∧
    (∀ {X Y : AlgebraicSpace S} (f : X ⟶ Y),
      P f ↔ ∀ x : Points X, existsEtaleSmoothSquareAt P f x) :=
  sorry

/-- An étale-smooth-local-on-source-and-target property is preserved by
precomposition with an étale morphism. -/
theorem precomp [IsEtaleSmoothLocalAtSourceAndTarget P] {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (g : Y ⟶ Z) (hf : Etale f) (hg : P g) : P (f ≫ g) :=
  sorry

/-- An étale-smooth-local-on-source-and-target property is preserved by the
base-change projection `pullback.snd f g` along a smooth morphism. -/
theorem pullback_snd [IsEtaleSmoothLocalAtSourceAndTarget P]
    {X Y Y' : AlgebraicSpace S} (f : X ⟶ Y) (g : Y' ⟶ Y)
    (hg : Smooth g) (hf : P f) : P (pullback.snd f g) :=
  sorry

/-- A morphism has an étale-smooth-local-on-source-and-target property if and
only if the property holds on the top arrow of some commutative square with
smooth right vertical arrow, étale comparison into the fibre product, and
surjective left vertical arrow. -/
theorem iff_exists_surjective_square [IsEtaleSmoothLocalAtSourceAndTarget P]
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    P f ↔
      ∃ (U V : AlgebraicSpace S) (a : U ⟶ X) (b : V ⟶ Y) (h : U ⟶ V)
        (sq : CommSq h a b f),
          Smooth b ∧ Etale (etaleSmoothSquareLift sq) ∧ Surjective a ∧ P h :=
  sorry

/-- A morphism has an étale-smooth-local-on-source-and-target property if and
only if the top arrow of every commutative square with smooth right vertical
arrow and étale comparison `U ⟶ pullback f b` has the property. -/
theorem iff_forall_comparison [IsEtaleSmoothLocalAtSourceAndTarget P]
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    P f ↔
      ∀ {U V : AlgebraicSpace S} (a : U ⟶ X) (b : V ⟶ Y) (h : U ⟶ V)
        (sq : CommSq h a b f),
        Smooth b → Etale (etaleSmoothSquareLift sq) → P h :=
  sorry

/-- A morphism has an étale-smooth-local-on-source-and-target property if and
only if the property holds after base change along every member of some smooth
covering of the target. -/
theorem iff_exists_targetCover [IsEtaleSmoothLocalAtSourceAndTarget P]
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    P f ↔ ∃ 𝒰 : (smoothPrecoverage S).ZeroHypercover.{u} Y,
      ∀ i : 𝒰.I₀, P (pullback.snd f (𝒰.f i)) :=
  sorry

/-- A morphism has an étale-smooth-local-on-source-and-target property if and
only if every member of some étale covering of the source has the property after
composition with the morphism. -/
theorem iff_exists_sourceCover [IsEtaleSmoothLocalAtSourceAndTarget P]
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    P f ↔ ∃ 𝒰 : (@etalePrecoverage S).ZeroHypercover.{u} X,
      ∀ i : 𝒰.I₀, P (𝒰.f i ≫ f) :=
  sorry

/-- A morphism has an étale-smooth-local-on-source-and-target property if and
only if, after some smooth covering of the target, each base change admits an
étale source covering whose composites to the target-cover member have the
property. -/
theorem iff_exists_targetSourceCovers [IsEtaleSmoothLocalAtSourceAndTarget P]
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    P f ↔ ∃ 𝒰 : (smoothPrecoverage S).ZeroHypercover.{u} Y, ∀ i : 𝒰.I₀,
      ∃ 𝒱 : (@etalePrecoverage S).ZeroHypercover.{u} (pullback f (𝒰.f i)),
        ∀ j : 𝒱.I₀, P (𝒱.f j ≫ pullback.snd f (𝒰.f i)) :=
  sorry

end IsEtaleSmoothLocalAtSourceAndTarget

end AlgebraicGeometry.AlgebraicSpace

