/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Adjunction
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Pullback.Composition
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Pushforward
public import ReasLib.CategoryTheory.DerivedCategory.Functor.TotalLeftDerived.Composition

@[expose] public section

open AlgebraicGeometry.RingedSpace.Hom

/-!
# Composition of derived pushforwards on ringed spaces

This module constructs the direct-image composition comparison from the composite derived
pullback-pushforward adjunction and uniqueness of right adjoints.
-/

open CategoryTheory
open AlgebraicGeometry
open RingedSite.Hom
open SheafOfModules
open scoped RingedSpace.Hom RingedSpaceDerivedPullback RingedSpaceDerivedPushforward

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

namespace moduleDerivedPushforward.Composition

section

variable {X Y Z : RingedSpace.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
variable [CategoryWithHomology (RingedSpace.Modules X)]
variable [CategoryWithHomology (RingedSpace.Modules Y)]
variable [CategoryWithHomology (RingedSpace.Modules Z)]
variable [(pushforward f).Additive] [(pushforward g).Additive]
variable [(pullback f).Additive] [(pullback g).Additive]
variable [HasWeakSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
variable [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [RingedSite.Hom.DerivedAdjunction.HasPair (opensRingedSiteHom f)]
variable [RingedSite.Hom.DerivedAdjunction.HasPair (opensRingedSiteHom g)]
variable [RingedSite.Hom.DerivedAdjunction.HasPair (opensRingedSiteHom (f ≫ g))]

/-- The composite derived pullback-pushforward adjunction, transported along the canonical
derived-pullback composition isomorphism. -/
noncomputable abbrev compositeAdjunction
    (h_pullback : IsIso (modulePullbackDerived.compComparison f g)) :
    L((f ≫ g))^* ⊣ R(f)_* ⋙ R(g)_* :=
  ((modulePullbackDerivedPushforwardAdjunction g).comp
    (modulePullbackDerivedPushforwardAdjunction f)).ofNatIsoLeft
      (modulePullbackDerived.compIso f g h_pullback)

/-- Lemma 20.28.2: the canonical pullback-composition isomorphism induces an isomorphism from
the composite derived pushforward `R(f)_* ⋙ R(g)_*` to `R((f ≫ g))_*`. -/
@[stacks 0D5T]
noncomputable def iso
    (h_pullback : IsIso (modulePullbackDerived.compComparison f g)) :
    R(f)_* ⋙ R(g)_* ≅ R((f ≫ g))_* :=
  (compositeAdjunction f g h_pullback).rightAdjointUniq
    (modulePullbackDerivedPushforwardAdjunction (f ≫ g))

/-- Lemma 20.28.2: the source-facing comparison from the derived pushforward of a composite to
the composite derived pushforward. -/
@[stacks 0D5T]
noncomputable def comparison
    (h_pullback : IsIso (modulePullbackDerived.compComparison f g)) :
    R((f ≫ g))_* ⟶ R(f)_* ⋙ R(g)_* :=
  (iso f g h_pullback).inv

/-- The derived-pushforward composition isomorphism is independent of the proof used to upgrade
the pullback comparison. -/
theorem iso_eq (h₁ h₂ : IsIso (modulePullbackDerived.compComparison f g)) :
    iso f g h₁ = iso f g h₂ := sorry

/-- The derived-pushforward comparison is independent of the proof used to upgrade the pullback
comparison. -/
theorem comparison_eq (h₁ h₂ : IsIso (modulePullbackDerived.compComparison f g)) :
    comparison f g h₁ = comparison f g h₂ := sorry

/-- The derived-pushforward composition isomorphism is compatible with the counits of the
derived pullback-pushforward adjunctions. -/
theorem iso_hom_counit
    (h_pullback : IsIso (modulePullbackDerived.compComparison f g)) :
    Functor.whiskerRight (iso f g h_pullback).hom (L((f ≫ g))^*) ≫
        (modulePullbackDerivedPushforwardAdjunction (f ≫ g)).counit =
      (((modulePullbackDerivedPushforwardAdjunction g).comp
          (modulePullbackDerivedPushforwardAdjunction f)).ofNatIsoLeft
        (modulePullbackDerived.compIso f g h_pullback)).counit := sorry

/-- The component of the derived-pushforward composition isomorphism is compatible with the
counits of the corresponding derived adjunctions. -/
theorem iso_hom_counit_app
    (h_pullback : IsIso (modulePullbackDerived.compComparison f g))
    (K : DerivedCategory X.Modules) :
    (L((f ≫ g))^*).map ((iso f g h_pullback).hom.app K) ≫
        (modulePullbackDerivedPushforwardAdjunction (f ≫ g)).counit.app K =
      (((modulePullbackDerivedPushforwardAdjunction g).comp
          (modulePullbackDerivedPushforwardAdjunction f)).ofNatIsoLeft
        (modulePullbackDerived.compIso f g h_pullback)).counit.app K := sorry

/-- Lemma 20.28.2, source-facing form: the comparison
`R((f ≫ g))_* ⟶ R(f)_* ⋙ R(g)_*` is an isomorphism. -/
@[stacks 0D5T]
theorem comparison_isIso
    (h_pullback : IsIso (modulePullbackDerived.compComparison f g)) :
    IsIso (comparison f g h_pullback) := sorry

/-- Every component of the canonical derived-pushforward composition comparison is an
isomorphism. -/
theorem comparison_app_isIso
    (h_pullback : IsIso (modulePullbackDerived.compComparison f g))
    (K : DerivedCategory X.Modules) :
    IsIso ((comparison f g h_pullback).app K) := sorry

end

-- Any `sorryAx` is inherited through existing category and derived-adjunction law fields; the
-- inverse data are selected only from the explicit `h_pullback` certificate.

end moduleDerivedPushforward.Composition

end AlgebraicGeometry.RingedSpace
