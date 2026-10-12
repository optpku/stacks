/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Basic
public import ReasLib.CategoryTheory.Adjunction.HomotopyCategory
public import ReasLib.CategoryTheory.Functor.Derived.Adjunction.Restriction

@[expose] public section

/-!
# Derived pullback-pushforward adjunctions on ringed sites

The total left- and right-derived functors form an adjunction once their two composite-derived
universal properties are supplied.  Those properties are packaged by the generic
`CategoryTheory.Adjunction.TotalDerived.HasPair`; they remain an explicit input until proved, so
proof debt never selects observable unit or counit data.
-/

open CategoryTheory
open ComplexShape

noncomputable section

universe z uX vX uY vY w

namespace RingedSite.Hom

namespace DerivedAdjunction

variable {X : RingedSite.{uX, vX, w}} {Y : RingedSite.{uY, vY, w}}

/-- The two absolute-derived conditions required to form the canonical adjunction between total
derived module pullback and pushforward. -/
@[stacks 07A6 "ringed-site total-derived adjunction pair"]
abbrev HasPair (f : Hom X Y)
    [UnivLE.{max uX vX, z}] [UnivLE.{max uY vY, z}]
    [(f.modulePushforward.{z}).IsRightAdjoint]
    [Functor.HasRightDerivedFunctor
      (modulePushforwardToDerived.{z} f) (ModuleQis.{z} X)]
    [Functor.HasLeftDerivedFunctor
      (modulePullbackToDerived.{z} f) (ModuleQis.{z} Y)] : Prop :=
  CategoryTheory.Adjunction.TotalDerived.HasPair
    (G := (modulePullback.{z} f).mapHomotopyCategory (up ℤ))
    (F := (modulePushforward.{z} f).mapHomotopyCategory (up ℤ))
    (ModuleQis.{z} Y) (ModuleQis.{z} X)
    (L1 := moduleLocalization.{z} Y) (L2 := moduleLocalization.{z} X)

end DerivedAdjunction

section

variable {X : RingedSite.{uX, vX, w}} {Y : RingedSite.{uY, vY, w}} (f : Hom X Y)
variable [UnivLE.{max uX vX, z}] [UnivLE.{max uY vY, z}]
variable [(f.modulePushforward.{z}).IsRightAdjoint]
variable [Functor.HasRightDerivedFunctor
  (modulePushforwardToDerived.{z} f) (ModuleQis.{z} X)]
variable [Functor.HasLeftDerivedFunctor
  (modulePullbackToDerived.{z} f) (ModuleQis.{z} Y)]

/-- The canonical adjunction between total derived module pullback and pushforward, from an
explicit absolute-derived pair certificate. -/
@[stacks 07A6 "derived pullback-pushforward adjunction"]
noncomputable def moduleDerivedAdjunction [DerivedAdjunction.HasPair.{z} f] :
    modulePullbackDerived.{z} f ⊣ modulePushforwardDerived.{z} f :=
  CategoryTheory.Adjunction.TotalDerived.HasPair.derived
    (Adjunction.mapHomotopyCategoryAdjunction
      (modulePullbackPushforwardAdjunction.{z} f))
      (ModuleQis.{z} Y) (ModuleQis.{z} X)

/- The short name above is the canonical owner.  The two aliases below preserve established
descriptive spellings; they carry no additional data and inherit the same explicit
`DerivedAdjunction.HasPair` certificate. -/

/-- The canonical derived pullback--pushforward adjunction under its descriptive spelling. -/
@[stacks 07A6 "derived pullback-pushforward adjunction bridge"]
noncomputable abbrev modulePullbackDerivedPushforwardAdjunction
    [DerivedAdjunction.HasPair.{z} f] :
    modulePullbackDerived.{z} f ⊣ modulePushforwardDerived.{z} f :=
  moduleDerivedAdjunction.{z} f

/-- A deprecated spelling of the canonical derived pullback--pushforward adjunction. -/
@[deprecated modulePullbackDerivedPushforwardAdjunction (since := "2026-08-04")]
noncomputable abbrev modulePullbackDerived_pushforward_adjunction
    [DerivedAdjunction.HasPair.{z} f] :
    modulePullbackDerived.{z} f ⊣ modulePushforwardDerived.{z} f :=
  modulePullbackDerivedPushforwardAdjunction.{z} f

/-- The derived adjunction does not depend on the supplied proof of the absolute-derived pair
condition. -/
@[stacks 07A6 "derived adjunction proof independence"]
theorem DerivedAdjunction.eq (h₁ h₂ : DerivedAdjunction.HasPair.{z} f) :
    -- Local instance justification (instance diamond): compare the adjunction data selected by
    -- two proofs of the same pair condition without choosing a global proof.
    (letI := h₁; moduleDerivedAdjunction.{z} f) =
      (letI := h₂; moduleDerivedAdjunction.{z} f) := sorry

/-- Derived inverse image along a morphism of ringed sites is a left adjoint whenever the total
derived pair condition holds. -/
theorem modulePullbackDerived_isLeftAdjoint [DerivedAdjunction.HasPair.{z} f] :
    (modulePullbackDerived.{z} f).IsLeftAdjoint :=
  (moduleDerivedAdjunction.{z} f).isLeftAdjoint

/-- Derived direct image along a morphism of ringed sites is a right adjoint whenever the total
derived pair condition holds. -/
theorem modulePushforwardDerived_isRightAdjoint [DerivedAdjunction.HasPair.{z} f] :
    (modulePushforwardDerived.{z} f).IsRightAdjoint :=
  (moduleDerivedAdjunction.{z} f).isRightAdjoint

end

end RingedSite.Hom
