module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.LocalizedChern.EnlargeCenter

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.LocalizedChern

/- Lemma 42.50.8 (1): for nested closed centers, the localized Newton class for
the larger center is the proper pushforward of the canonical class for the smaller center. -/
@[stacks 0FB7] #check
  (AlgebraicGeometry.LocalizedChern.localizedNewtonClass_eq_pushforward :
    ∀ {S : Scheme.{u}} [UniversallyCatenary S] {δ : S → ℤ} [IsDimensionFunction δ]
    {X : Over S} [LocallyOfFiniteType X.hom] {Z Z' : Scheme.{u}}
    (j : Z ⟶ Z') (i : Z' ⟶ X.left)
    [IsClosedImmersion j] [IsClosedImmersion i]
    (classes : ChernClass.Theory δ X.hom)
    {E : RingedSpace.ModuleDerived X.left.toRingedSpace} {p : ℕ}
    (situation : Situation S δ X (j ≫ i) E p .vanishing),
    newtonClass i classes E situation.perfect
        (Situation.enlargeCenter j i situation).offCenter situation.finiteness p
      =
      BivariantClass.properPushforward δ
        (Over.homMk j (Category.assoc j i X.hom).symm :
          Over.mk ((j ≫ i) ≫ X.hom) ⟶ Over.mk (i ≫ X.hom))
        (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X) (p : ℤ)
        ((Over.homMk_eta
          ((Over.homMk j (Category.assoc j i X.hom).symm :
              Over.mk ((j ≫ i) ≫ X.hom) ⟶ Over.mk (i ≫ X.hom)) ≫
            (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X))
          (Eq.refl ((j ≫ i) ≫ X.hom))) ▸
            newtonClass (j ≫ i) classes E situation.perfect situation.offCenter
              situation.finiteness p))

/- Lemma 42.50.8 (2): for nested closed centers, the localized `p`th Chern class for
the larger center is the proper pushforward of the canonical class for the smaller center. -/
@[stacks 0FB7] #check
  (AlgebraicGeometry.LocalizedChern.localizedChernClass_eq_pushforward :
    ∀ {S : Scheme.{u}} [UniversallyCatenary S] {δ : S → ℤ} [IsDimensionFunction δ]
    {X : Over S} [LocallyOfFiniteType X.hom] {Z Z' : Scheme.{u}}
    (j : Z ⟶ Z') (i : Z' ⟶ X.left)
    [IsClosedImmersion j] [IsClosedImmersion i]
    (classes : ChernClass.Theory δ X.hom)
    {E : RingedSpace.ModuleDerived X.left.toRingedSpace} {p : ℕ}
    (situation : Situation S δ X (j ≫ i) E p .rankBound),
    chernClass i classes E situation.perfect p
        (Situation.enlargeCenter j i situation).offCenter situation.finiteness
      =
      BivariantClass.properPushforward δ
        (Over.homMk j (Category.assoc j i X.hom).symm :
          Over.mk ((j ≫ i) ≫ X.hom) ⟶ Over.mk (i ≫ X.hom))
        (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X) (p : ℤ)
        ((Over.homMk_eta
          ((Over.homMk j (Category.assoc j i X.hom).symm :
              Over.mk ((j ≫ i) ≫ X.hom) ⟶ Over.mk (i ≫ X.hom)) ≫
            (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X))
          (Eq.refl ((j ≫ i) ≫ X.hom))) ▸
            chernClass (j ≫ i) classes E situation.perfect p situation.offCenter
              situation.finiteness))

end AlgebraicGeometry.LocalizedChern
