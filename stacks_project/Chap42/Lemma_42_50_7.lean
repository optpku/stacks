module

public import ReasLib.AlgebraicGeometry.LocalizedChern.DisjointSupport
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.LocalizedChern

/- Lemma 42.50.7 (1): the localized Newton class acts trivially on a Chow class
carried by a closed support disjoint from the center. -/
@[stacks 0FB6]
#check (AlgebraicGeometry.LocalizedChern.newtonClass_cap_eq_zero_of_disjoint_support :
    ∀ {S : Scheme.{u}} [UniversallyCatenary S] {δ : S → ℤ} [IsDimensionFunction δ]
    {X : Over S} [LocallyOfFiniteType X.hom] {Z : Scheme.{u}}
    (i : Z ⟶ X.left) [IsClosedImmersion i]
    (classes : ChernClass.Theory δ X.hom)
    {E : RingedSpace.ModuleDerived X.left.toRingedSpace} {p : ℕ}
    (situation : Situation S δ X i E p .vanishing) (k : ℤ)
    (α : ChowGroup.Supported X.hom δ k)
    (hα : Disjoint (α.support : Set X.left) (Set.range i.base)),
    (newtonClass i classes E situation.perfect situation.offCenter
        situation.finiteness p).cap
      (𝟙 (Over.mk (i ≫ X.hom))) (Over.homMk i) (𝟙 X)
      (IsPullback.id_horiz i) k α.toAmbient = 0)

/- Lemma 42.50.7 (2): the localized `p`th Chern class acts trivially on a Chow
class carried by a closed support disjoint from the center. -/
@[stacks 0FB6]
#check (AlgebraicGeometry.LocalizedChern.chernClass_cap_eq_zero_of_disjoint_support :
    ∀ {S : Scheme.{u}} [UniversallyCatenary S] {δ : S → ℤ} [IsDimensionFunction δ]
    {X : Over S} [LocallyOfFiniteType X.hom] {Z : Scheme.{u}}
    (i : Z ⟶ X.left) [IsClosedImmersion i]
    (classes : ChernClass.Theory δ X.hom)
    {E : RingedSpace.ModuleDerived X.left.toRingedSpace} {p : ℕ}
    (situation : Situation S δ X i E p .rankBound) (k : ℤ)
    (α : ChowGroup.Supported X.hom δ k)
    (hα : Disjoint (α.support : Set X.left) (Set.range i.base)),
    (chernClass i classes E situation.perfect p situation.offCenter
        situation.finiteness).cap
      (𝟙 (Over.mk (i ≫ X.hom))) (Over.homMk i) (𝟙 X)
      (IsPullback.id_horiz i) k α.toAmbient = 0)

end AlgebraicGeometry.LocalizedChern
