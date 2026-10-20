module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.ChowCohomology.ChernClass.Derived.Dual

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.ChernClass.Derived

open RingedSpace.ModuleDerived

/- Lemma 42.46.9: the degree-`i` Chern class of the derived dual is `(-1) ^ i` times the original class. -/
@[stacks 0FAE]
#check
  (AlgebraicGeometry.ChernClass.Derived.totalClass_dual :
    ∀ {S X : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (π : X ⟶ S) [LocallyOfFiniteType π]
    [KFlat.HomotopyTensorDescends X.toRingedSpace]
    [KFlat.TensorDescends X.toRingedSpace]
    [KFlat.IsLocalization X.toRingedSpace]
    [MonoidalClosed (RingedSpace.ModuleDerived X.toRingedSpace)]
    (classes : ChernClass.Theory δ π) (E : RingedSpace.ModuleDerived X.toRingedSpace)
    (hPerfect : RingedSpace.ModuleDerived.IsPerfect E) (hDefined : IsDefined E) (i : ℕ),
    totalClass δ π classes (MonoidalClosed.dual E) hPerfect.dual
        (hDefined.dual hPerfect) i =
      ((-1 : ℤ) ^ i) • totalClass δ π classes E hPerfect hDefined i)

/- Lemma 42.46.9: the degree-`i` Newton class of the derived dual is `(-1) ^ i` times the original class. -/
@[stacks 0FAE]
#check
  (AlgebraicGeometry.ChernClass.Derived.newtonClass_dual :
    ∀ {S X : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (π : X ⟶ S) [LocallyOfFiniteType π]
    [KFlat.HomotopyTensorDescends X.toRingedSpace]
    [KFlat.TensorDescends X.toRingedSpace]
    [KFlat.IsLocalization X.toRingedSpace]
    [MonoidalClosed (RingedSpace.ModuleDerived X.toRingedSpace)]
    (classes : ChernClass.Theory δ π) (E : RingedSpace.ModuleDerived X.toRingedSpace)
    (hPerfect : RingedSpace.ModuleDerived.IsPerfect E) (hDefined : IsDefined E) (i : ℕ),
    newtonClass δ π classes (MonoidalClosed.dual E) hPerfect.dual
        (hDefined.dual hPerfect) i =
      ((-1 : ℤ) ^ i) • newtonClass δ π classes E hPerfect hDefined i)

/- Lemma 42.46.9: the degree-`i` rational Chern character of the derived dual is `(-1) ^ i` times the original character. -/
@[stacks 0FAE]
#check
  (AlgebraicGeometry.ChernClass.Derived.character_dual :
    ∀ {S X : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (π : X ⟶ S) [LocallyOfFiniteType π]
    [KFlat.HomotopyTensorDescends X.toRingedSpace]
    [KFlat.TensorDescends X.toRingedSpace]
    [KFlat.IsLocalization X.toRingedSpace]
    [MonoidalClosed (RingedSpace.ModuleDerived X.toRingedSpace)]
    (classes : ChernClass.Theory δ π) (E : RingedSpace.ModuleDerived X.toRingedSpace)
    (hPerfect : RingedSpace.ModuleDerived.IsPerfect E) (hDefined : IsDefined E) (i : ℕ),
    character δ π classes (MonoidalClosed.dual E) hPerfect.dual
        (hDefined.dual hPerfect) i =
      ((-1 : ℤ) ^ i) • character δ π classes E hPerfect hDefined i)

end AlgebraicGeometry.ChernClass.Derived
