/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.LocalizedChern.Classes
public import ReasLib.AlgebraicGeometry.BivariantClass.ProperPushforward
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.ClosedImmersion.Proper

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.LocalizedChern

namespace Situation

/-- Enlarging a closed center preserves either off-center condition in a localized-Chern
situation. -/
theorem enlargeCenter
    {S : Scheme.{u}} [UniversallyCatenary S] {δ : S → ℤ} [IsDimensionFunction δ]
    {X : Over S} [LocallyOfFiniteType X.hom] {Z Z' : Scheme.{u}}
    (j : Z ⟶ Z') (i : Z' ⟶ X.left)
    [IsClosedImmersion j] [IsClosedImmersion i]
    {E : RingedSpace.ModuleDerived X.left.toRingedSpace} {p : ℕ}
    {mode : RestrictionBehavior}
    (situation : Situation S δ X (j ≫ i) E p mode) :
    Situation S δ X i E p mode := sorry

end Situation

/-- For nested closed centers, the canonical localized Newton class supported on the
larger center is the proper pushforward of the class supported on the smaller center. -/
theorem localizedNewtonClass_eq_pushforward
    {S : Scheme.{u}} [UniversallyCatenary S] {δ : S → ℤ} [IsDimensionFunction δ]
    {X : Over S} [LocallyOfFiniteType X.hom] {Z Z' : Scheme.{u}}
    (j : Z ⟶ Z') (i : Z' ⟶ X.left)
    [IsClosedImmersion j] [IsClosedImmersion i]
    (classes : ChernClass.Theory δ X.hom)
    {E : RingedSpace.ModuleDerived X.left.toRingedSpace} {p : ℕ}
    (situation : Situation S δ X (j ≫ i) E p .vanishing) :
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
              situation.finiteness p) := sorry

/-- For nested closed centers, the canonical localized `p`th Chern class supported on the
larger center is the proper pushforward of the class supported on the smaller center. -/
theorem localizedChernClass_eq_pushforward
    {S : Scheme.{u}} [UniversallyCatenary S] {δ : S → ℤ} [IsDimensionFunction δ]
    {X : Over S} [LocallyOfFiniteType X.hom] {Z Z' : Scheme.{u}}
    (j : Z ⟶ Z') (i : Z' ⟶ X.left)
    [IsClosedImmersion j] [IsClosedImmersion i]
    (classes : ChernClass.Theory δ X.hom)
    {E : RingedSpace.ModuleDerived X.left.toRingedSpace} {p : ℕ}
    (situation : Situation S δ X (j ≫ i) E p .rankBound) :
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
              situation.finiteness) := sorry

end AlgebraicGeometry.LocalizedChern
