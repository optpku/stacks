module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Pushforward.Adjunction
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.LowerShriek.Adjunction
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Support
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ElementaryDistinguishedSquare

/-! # Derived adjunction isomorphisms with support

On an elementary distinguished square, support on the closed complement makes the
canonical derived adjunction maps and the lower-shriek-to-pushforward comparison invertible.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules
open AlgebraicGeometry.AlgebraicSpace.ModuleDerived
open AlgebraicGeometry.AlgebraicSpace.IsElementaryDistinguishedSquare

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

variable {S : Scheme.{u}} {U V X : AlgebraicSpace S}

/-- The derived restriction–pushforward unit is invertible on a module supported on the
complement of the open subspace in an elementary distinguished square. -/
theorem isIso_restrictPushforwardDerived_unit (j : U ⟶ X) [Etale j] (f : V ⟶ X) [Etale f]
    [IsElementaryDistinguishedSquare j f] (E : ModuleDerived X)
    (hE : IsSupportedOn E (toOpenSubspace j f).pointsSetᶜ) :
    IsIso ((restrictPushforwardDerivedAdjunction f).unit.app E) :=
  sorry

/-- The derived lower-shriek counit is invertible on a module supported on the
complement of the open subspace in an elementary distinguished square. -/
theorem isIso_lowerShriekDerived_counit (j : U ⟶ X) [Etale j] (f : V ⟶ X) [Etale f]
    [IsElementaryDistinguishedSquare j f] (E : ModuleDerived X)
    (hE : IsSupportedOn E (toOpenSubspace j f).pointsSetᶜ) :
    IsIso ((lowerShriekDerivedAdjunction f).counit.app E) :=
  sorry

/-- The derived lower-shriek unit is invertible on a module supported above the
complement of the open subspace in an elementary distinguished square. -/
theorem isIso_lowerShriekDerived_unit (j : U ⟶ X) [Etale j] (f : V ⟶ X) [Etale f]
    [IsElementaryDistinguishedSquare j f] (F : ModuleDerived V)
    (hF : IsSupportedOn F (Points.map f ⁻¹' (toOpenSubspace j f).pointsSetᶜ)) :
    IsIso ((lowerShriekDerivedAdjunction f).unit.app F) :=
  sorry

/-- The derived restriction–pushforward counit is invertible on a module supported above
the complement of the open subspace in an elementary distinguished square. -/
theorem isIso_restrictPushforwardDerived_counit (j : U ⟶ X) [Etale j] (f : V ⟶ X) [Etale f]
    [IsElementaryDistinguishedSquare j f] (F : ModuleDerived V)
    (hF : IsSupportedOn F (Points.map f ⁻¹' (toOpenSubspace j f).pointsSetᶜ)) :
    IsIso ((restrictPushforwardDerivedAdjunction f).counit.app F) :=
  sorry

/-- For a module supported above the closed complement in an elementary distinguished
square, there is a unique lower-shriek-to-pushforward morphism whose adjunction transpose
is the two-sided inverse of the lower-shriek unit, and this morphism is invertible. -/
theorem existsUnique_lowerShriekDerived_pushforwardDerived_comparison
    (j : U ⟶ X) [Etale j] (f : V ⟶ X) [Etale f]
    [IsElementaryDistinguishedSquare j f] (F : ModuleDerived V)
    (hF : IsSupportedOn F (Points.map f ⁻¹' (toOpenSubspace j f).pointsSetᶜ)) :
    ∃! c : (lowerShriekDerived f).obj F ⟶ (moduleDerivedPushforward f).obj F,
      let a := ((restrictPushforwardDerivedAdjunction f).homEquiv
        ((lowerShriekDerived f).obj F) F).symm c
      ((lowerShriekDerivedAdjunction f).unit.app F ≫ a = 𝟙 F) ∧
        (a ≫ (lowerShriekDerivedAdjunction f).unit.app F =
          𝟙 ((restrictFunctorDerived f).obj ((lowerShriekDerived f).obj F))) ∧
        IsIso c :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules
