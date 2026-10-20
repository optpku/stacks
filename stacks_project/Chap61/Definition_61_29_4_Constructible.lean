/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.ProEtale.DerivedAdicSheaf

/-!
# Compatibility surface for derived adic constructible objects
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

universe u w

namespace AlgebraicGeometry.Scheme.ProEt

namespace Derived

variable {X : Scheme.{u}} {Λ : Type w} [CommRing Λ] [IsNoetherianRing Λ]
variable [HasWeakSheafify (topology X) (ModuleCat.{w} Λ)]
variable [∀ U : X.ProEt, HasWeakSheafify ((topology X).over U) (ModuleCat.{w} Λ)]
variable [Abelian (Sheaf (topology X) (ModuleCat.{w} Λ))]
variable [∀ U : X.ProEt, Abelian (Sheaf ((topology X).over U) (ModuleCat.{w} Λ))]
variable [HasDerivedCategory (Sheaf (topology X) (ModuleCat.{w} Λ))]
variable [∀ U : X.ProEt, HasDerivedCategory (Sheaf ((topology X).over U) (ModuleCat.{w} Λ))]
variable [∀ U : X.ProEt, ((topology X).overPullback (ModuleCat.{w} Λ) U).Additive]
variable [∀ U : X.ProEt, PreservesFiniteLimits ((topology X).overPullback (ModuleCat.{w} Λ) U)]
variable [∀ U : X.ProEt, PreservesFiniteColimits ((topology X).overPullback (ModuleCat.{w} Λ) U)]
variable [HasTerminal X.ProEt]
variable [∀ {Y : Scheme.{u}}, HasWeakSheafify (topology Y) (ModuleCat.{w} Λ)]
variable [∀ {Y : Scheme.{u}} (U : Y.ProEt),
  HasWeakSheafify ((topology Y).over U) (ModuleCat.{w} Λ)]
variable [∀ {Y : Scheme.{u}}, Abelian (Sheaf (topology Y) (ModuleCat.{w} Λ))]
variable [∀ {Y : Scheme.{u}} (U : Y.ProEt),
  Abelian (Sheaf ((topology Y).over U) (ModuleCat.{w} Λ))]
variable [∀ {Y : Scheme.{u}}, HasDerivedCategory (Sheaf (topology Y) (ModuleCat.{w} Λ))]
variable [∀ {Y : Scheme.{u}} (U : Y.ProEt),
  HasDerivedCategory (Sheaf ((topology Y).over U) (ModuleCat.{w} Λ))]
variable [∀ {Y : Scheme.{u}} (U : Y.ProEt),
  ((topology Y).overPullback (ModuleCat.{w} Λ) U).Additive]
variable [∀ {Y : Scheme.{u}} (U : Y.ProEt),
  PreservesFiniteLimits ((topology Y).overPullback (ModuleCat.{w} Λ) U)]
variable [∀ {Y : Scheme.{u}} (U : Y.ProEt),
  PreservesFiniteColimits ((topology Y).overPullback (ModuleCat.{w} Λ) U)]
variable [∀ {Y : Scheme.{u}}, HasTerminal Y.ProEt]
variable [∀ {Y : Scheme.{u}} (f : Y ⟶ X) (P : X.ProEtᵒᵖ ⥤ ModuleCat.{w} Λ),
  (baseChange f).op.HasLeftKanExtension P]
variable (I : Ideal Λ) (K : DerivedCategory (Sheaf (topology X) (ModuleCat.{w} Λ)))

/- The shared derived adic constructible predicate is available under the established API. -/
#check (AlgebraicGeometry.Scheme.ProEt.Derived.IsAdicConstructible
  (I := I) (K := K) : Prop)

end Derived

end AlgebraicGeometry.Scheme.ProEt
