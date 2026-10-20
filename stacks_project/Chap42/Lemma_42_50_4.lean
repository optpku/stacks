module

public import ReasLib.AlgebraicGeometry.LocalizedChern.BaseChange
public import stacks_project.Chap42.Definition_42_50_3_LocalizedClasses
public import stacks_project.Chap42.«42_50_2_1_BivariantPushforward»
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.LocalizedChern

#check (AlgebraicGeometry.LocalizedChern.Situation.pullback :
  ∀ {S : Scheme.{u}} [UniversallyCatenary S] {δ : S → ℤ} [IsDimensionFunction δ]
    {X X' : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType X'.hom]
    {Z Z' : Scheme.{u}} (i : Z ⟶ X.left) [IsClosedImmersion i]
    (i' : Z' ⟶ X'.left) [IsClosedImmersion i']
    (f : X' ⟶ X) [LocallyOfFiniteType f.left]
    (fZ : Over.mk (i' ≫ X'.hom) ⟶ Over.mk (i ≫ X.hom))
    (square : IsPullback fZ.left
      (Over.homMk i' : Over.mk (i' ≫ X'.hom) ⟶ X').left
      (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X).left f.left)
    {E : RingedSpace.ModuleDerived X.left.toRingedSpace} {p : ℕ}
    {mode : RestrictionBehavior} (situation : Situation S δ X i E p mode),
    Situation S δ X' i'
      ((RingedSpace.modulePullbackDerived f.left.toShHom).obj E) p mode)

/- Lemma 42.50.4 (1): localized Newton classes commute with locally finite-type
base change. -/
@[stacks 0FB3] #check (AlgebraicGeometry.LocalizedChern.newtonClass_restrict :
  ∀ {S : Scheme.{u}} [UniversallyCatenary S] {δ : S → ℤ} [IsDimensionFunction δ]
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
    (situation : Situation S δ X i E p .vanishing),
    let E' := (RingedSpace.modulePullbackDerived f.left.toShHom).obj E
    let situation' := Situation.pullback i i' f fZ square situation
    BivariantClass.restrict δ fZ
        (Over.homMk i' : Over.mk (i' ≫ X'.hom) ⟶ X') f square (p : ℤ)
        (newtonClass i classes E situation.perfect situation.offCenter
          situation.finiteness p) =
      newtonClass i' (classes.reanchor X') E' situation'.perfect situation'.offCenter
        situation'.finiteness p)

/- Lemma 42.50.4 (2): localized Chern classes commute with locally finite-type
base change. -/
@[stacks 0FB3] #check (AlgebraicGeometry.LocalizedChern.chernClass_restrict :
  ∀ {S : Scheme.{u}} [UniversallyCatenary S] {δ : S → ℤ} [IsDimensionFunction δ]
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
    (situation : Situation S δ X i E p .rankBound),
    let E' := (RingedSpace.modulePullbackDerived f.left.toShHom).obj E
    let situation' := Situation.pullback i i' f fZ square situation
    BivariantClass.restrict δ fZ
        (Over.homMk i' : Over.mk (i' ≫ X'.hom) ⟶ X') f square (p : ℤ)
        (chernClass i classes E situation.perfect p situation.offCenter
          situation.finiteness) =
      chernClass i' (classes.reanchor X') E' situation'.perfect p situation'.offCenter
        situation'.finiteness)

end AlgebraicGeometry.LocalizedChern
