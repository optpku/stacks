/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Adjunction
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Pullback.TotalComposition
public import Mathlib.CategoryTheory.Adjunction.Unique

/-! # Composition of derived module pushforwards -/

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

/-- The canonical identification of the composite derived pushforward with derived
pushforward along a composite morphism, obtained from uniqueness of right adjoints
after transporting the composite adjunction along the derived-pullback composition
comparison. -/
noncomputable def pushforwardDerived.compIso {S : Scheme.{u}}
    {X Y Z : AlgebraicSpace S} (f : X ⟶ Y) (g : Y ⟶ Z) :
    moduleDerivedPushforward f ⋙ moduleDerivedPushforward g ≅ moduleDerivedPushforward (f ≫ g) :=
  (((Modules.derivedPullbackPushforwardAdjunction g).comp
      (Modules.derivedPullbackPushforwardAdjunction f)).ofNatIsoLeft
        (ModuleDerived.totalPullbackCompIso f g)).rightAdjointUniq
    (Modules.derivedPullbackPushforwardAdjunction (f ≫ g))

/-- The derived-pushforward composition isomorphism is the uniqueness isomorphism
between the transported composite adjunction and derived pushforward along the
composite morphism. -/
theorem pushforwardDerived.compIso_eq {S : Scheme.{u}}
    {X Y Z : AlgebraicSpace S} (f : X ⟶ Y) (g : Y ⟶ Z) :
    pushforwardDerived.compIso f g =
      (((Modules.derivedPullbackPushforwardAdjunction g).comp
          (Modules.derivedPullbackPushforwardAdjunction f)).ofNatIsoLeft
            (ModuleDerived.totalPullbackCompIso f g)).rightAdjointUniq
        (Modules.derivedPullbackPushforwardAdjunction (f ≫ g)) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules

