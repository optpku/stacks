module

public import stacks_project.Chap42.«42_50_2_1_BivariantPushforward»
public import stacks_project.Chap42.Lemma_42_50_2_DefinedChern

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.LocalizedChern

/-- Lemma 42.50.2 (1): in the vanishing case there is a degree-`p` localized Newton
bivariant class on `Z ⟶ X` whose proper pushforward is the ambient Newton class of `E`. -/
@[stacks 0FB2]
theorem existsLocalizedNewtonClass
    {S : Scheme.{u}} [UniversallyCatenary S] {δ : S → ℤ} [IsDimensionFunction δ]
    {X : Over S} [LocallyOfFiniteType X.hom] {Z : Scheme.{u}}
    (i : Z ⟶ X.left) [IsClosedImmersion i]
    (classes : ChernClass.Theory δ X.hom)
    {E : RingedSpace.ModuleDerived X.left.toRingedSpace} {p : ℕ}
    (situation : Situation S δ X i E p .vanishing) :
    ∃ localized : BivariantClass δ
        (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X) (p : ℤ),
      BivariantClass.pushforwardToTarget δ
          (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X) (p : ℤ) localized =
        ChernClass.Derived.newtonClass δ X.hom classes E situation.perfect
          situation.isDefined p := sorry

/-- Lemma 42.50.2 (2): in the rank-bound case there is a degree-`p` localized Chern
bivariant class on `Z ⟶ X` whose proper pushforward is the ambient Chern class of `E`. -/
@[stacks 0FB2]
theorem existsLocalizedChernClass
    {S : Scheme.{u}} [UniversallyCatenary S] {δ : S → ℤ} [IsDimensionFunction δ]
    {X : Over S} [LocallyOfFiniteType X.hom] {Z : Scheme.{u}}
    (i : Z ⟶ X.left) [IsClosedImmersion i]
    (classes : ChernClass.Theory δ X.hom)
    {E : RingedSpace.ModuleDerived X.left.toRingedSpace} {p : ℕ}
    (situation : Situation S δ X i E p .rankBound) :
    ∃ localized : BivariantClass δ
        (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X) (p : ℤ),
      BivariantClass.pushforwardToTarget δ
          (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X) (p : ℤ) localized =
        ChernClass.Derived.totalClass δ X.hom classes E situation.perfect
          situation.isDefined p := sorry

end AlgebraicGeometry.LocalizedChern
