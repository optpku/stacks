/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap42.Definition_42_50_3_LocalizedClasses
public import stacks_project.Chap42.Remark_42_33_5_Bivariant

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.LocalizedChern

/-- Pulling a localized-Chern situation back along a locally finite-type cartesian
inverse-image square preserves its perfectness, off-center behavior, and technical
finiteness condition. -/
theorem Situation.pullback
    {S : Scheme.{u}} [UniversallyCatenary S] {δ : S → ℤ} [IsDimensionFunction δ]
    {X X' : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType X'.hom]
    {Z Z' : Scheme.{u}} (i : Z ⟶ X.left) [IsClosedImmersion i]
    (i' : Z' ⟶ X'.left) [IsClosedImmersion i']
    (f : X' ⟶ X) [LocallyOfFiniteType f.left]
    (fZ : Over.mk (i' ≫ X'.hom) ⟶ Over.mk (i ≫ X.hom))
    (square : IsPullback fZ.left
      (Over.homMk i' : Over.mk (i' ≫ X'.hom) ⟶ X').left
      (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X).left f.left)
    {E : RingedSpace.ModuleDerived X.left.toRingedSpace} {p : ℕ}
    {mode : RestrictionBehavior} (situation : Situation S δ X i E p mode) :
    Situation S δ X' i'
      ((RingedSpace.modulePullbackDerived f.left.toShHom).obj E) p mode := sorry

/-- Lemma 42.50.4 (1): the localized Newton class of the derived pullback to a
locally finite-type base change is the bivariant restriction of the original class. -/
@[stacks 0FB3]
theorem newtonClass_restrict
    {S : Scheme.{u}} [UniversallyCatenary S] {δ : S → ℤ} [IsDimensionFunction δ]
    (X X' : Over S) [LocallyOfFiniteType X.hom] [LocallyOfFiniteType X'.hom]
    {Z Z' : Scheme.{u}} (i : Z ⟶ X.left) [IsClosedImmersion i]
    (i' : Z' ⟶ X'.left) [IsClosedImmersion i']
    (f : X' ⟶ X) [LocallyOfFiniteType f.left]
    (fZ : Over.mk (i' ≫ X'.hom) ⟶ Over.mk (i ≫ X.hom))
    (square : IsPullback fZ.left
      (Over.homMk i' : Over.mk (i' ≫ X'.hom) ⟶ X').left
      (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X).left f.left)
    (classes : ChernClass.Theory δ X.hom)
    (E : RingedSpace.ModuleDerived X.left.toRingedSpace) (p : ℕ)
    (situation : Situation S δ X i E p .vanishing) :
    let E' := (RingedSpace.modulePullbackDerived f.left.toShHom).obj E
    let situation' := Situation.pullback i i' f fZ square situation
    BivariantClass.restrict δ fZ
        (Over.homMk i' : Over.mk (i' ≫ X'.hom) ⟶ X') f square (p : ℤ)
        (newtonClass i classes E situation.perfect situation.offCenter
          situation.finiteness p) =
      newtonClass i' (classes.reanchor X') E' situation'.perfect situation'.offCenter
        situation'.finiteness p := sorry

/-- Lemma 42.50.4 (2): the localized Chern class of the derived pullback to a
locally finite-type base change is the bivariant restriction of the original class. -/
@[stacks 0FB3]
theorem chernClass_restrict
    {S : Scheme.{u}} [UniversallyCatenary S] {δ : S → ℤ} [IsDimensionFunction δ]
    (X X' : Over S) [LocallyOfFiniteType X.hom] [LocallyOfFiniteType X'.hom]
    {Z Z' : Scheme.{u}} (i : Z ⟶ X.left) [IsClosedImmersion i]
    (i' : Z' ⟶ X'.left) [IsClosedImmersion i']
    (f : X' ⟶ X) [LocallyOfFiniteType f.left]
    (fZ : Over.mk (i' ≫ X'.hom) ⟶ Over.mk (i ≫ X.hom))
    (square : IsPullback fZ.left
      (Over.homMk i' : Over.mk (i' ≫ X'.hom) ⟶ X').left
      (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X).left f.left)
    (classes : ChernClass.Theory δ X.hom)
    (E : RingedSpace.ModuleDerived X.left.toRingedSpace) (p : ℕ)
    (situation : Situation S δ X i E p .rankBound) :
    let E' := (RingedSpace.modulePullbackDerived f.left.toShHom).obj E
    let situation' := Situation.pullback i i' f fZ square situation
    BivariantClass.restrict δ fZ
        (Over.homMk i' : Over.mk (i' ≫ X'.hom) ⟶ X') f square (p : ℤ)
        (chernClass i classes E situation.perfect p situation.offCenter
          situation.finiteness) =
      chernClass i' (classes.reanchor X') E' situation'.perfect p situation'.offCenter
        situation'.finiteness := sorry

end AlgebraicGeometry.LocalizedChern
