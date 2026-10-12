/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import stacks_project.Chap42.Remark_42_46_8
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Perfect.Duality

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.ChernClass.Derived

open RingedSpace.ModuleDerived

namespace IsDefined

/-- Definedness of Chern classes for a perfect derived `𝒪_X`-module is preserved by
the closed-monoidal dual. -/
theorem dual {X : Scheme.{u}}
    [KFlat.HomotopyTensorDescends X.toRingedSpace]
    [KFlat.TensorDescends X.toRingedSpace]
    [KFlat.IsLocalization X.toRingedSpace]
    [MonoidalClosed (RingedSpace.ModuleDerived X.toRingedSpace)]
    {E : RingedSpace.ModuleDerived X.toRingedSpace}
    (hDefined : IsDefined E) (hPerfect : RingedSpace.ModuleDerived.IsPerfect E) :
    IsDefined (MonoidalClosed.dual E) := sorry

end IsDefined

/-- Lemma 42.46.9 (1): the degree-`i` Chern class of the derived dual of a perfect
derived `𝒪_X`-module is `(-1) ^ i` times its degree-`i` Chern class. -/
@[stacks 0FAE]
theorem totalClass_dual
    {S X : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (π : X ⟶ S) [LocallyOfFiniteType π]
    [KFlat.HomotopyTensorDescends X.toRingedSpace]
    [KFlat.TensorDescends X.toRingedSpace]
    [KFlat.IsLocalization X.toRingedSpace]
    [MonoidalClosed (RingedSpace.ModuleDerived X.toRingedSpace)]
    (classes : ChernClass.Theory δ π) (E : RingedSpace.ModuleDerived X.toRingedSpace)
    (hPerfect : RingedSpace.ModuleDerived.IsPerfect E) (hDefined : IsDefined E) (i : ℕ) :
    totalClass δ π classes (MonoidalClosed.dual E) hPerfect.dual
        (hDefined.dual hPerfect) i =
      ((-1 : ℤ) ^ i) • totalClass δ π classes E hPerfect hDefined i := sorry

/-- Lemma 42.46.9 (2): the degree-`i` Newton class of the derived dual of a perfect
derived `𝒪_X`-module is `(-1) ^ i` times its degree-`i` Newton class. -/
@[stacks 0FAE]
theorem newtonClass_dual
    {S X : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (π : X ⟶ S) [LocallyOfFiniteType π]
    [KFlat.HomotopyTensorDescends X.toRingedSpace]
    [KFlat.TensorDescends X.toRingedSpace]
    [KFlat.IsLocalization X.toRingedSpace]
    [MonoidalClosed (RingedSpace.ModuleDerived X.toRingedSpace)]
    (classes : ChernClass.Theory δ π) (E : RingedSpace.ModuleDerived X.toRingedSpace)
    (hPerfect : RingedSpace.ModuleDerived.IsPerfect E) (hDefined : IsDefined E) (i : ℕ) :
    newtonClass δ π classes (MonoidalClosed.dual E) hPerfect.dual
        (hDefined.dual hPerfect) i =
      ((-1 : ℤ) ^ i) • newtonClass δ π classes E hPerfect hDefined i := sorry

/-- Lemma 42.46.9 (3): the degree-`i` Chern-character class of the derived dual of a
perfect derived `𝒪_X`-module is `(-1) ^ i` times its degree-`i` Chern-character class. -/
@[stacks 0FAE]
theorem character_dual
    {S X : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (π : X ⟶ S) [LocallyOfFiniteType π]
    [KFlat.HomotopyTensorDescends X.toRingedSpace]
    [KFlat.TensorDescends X.toRingedSpace]
    [KFlat.IsLocalization X.toRingedSpace]
    [MonoidalClosed (RingedSpace.ModuleDerived X.toRingedSpace)]
    (classes : ChernClass.Theory δ π) (E : RingedSpace.ModuleDerived X.toRingedSpace)
    (hPerfect : RingedSpace.ModuleDerived.IsPerfect E) (hDefined : IsDefined E) (i : ℕ) :
    character δ π classes (MonoidalClosed.dual E) hPerfect.dual
        (hDefined.dual hPerfect) i =
      ((-1 : ℤ) ^ i) • character δ π classes E hPerfect hDefined i := sorry

end AlgebraicGeometry.ChernClass.Derived
