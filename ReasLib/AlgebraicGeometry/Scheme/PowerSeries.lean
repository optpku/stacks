/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.RingTheory.PowerSeries.Ideal
public import ReasLib.AlgebraicGeometry.GroupScheme
public import ReasLib.AlgebraicGeometry.Scheme.OverField

/-!
# Schemes over a power-series ring
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

noncomputable section

universe u

namespace AlgebraicGeometry.HomStack

/-- The spectrum of the formal power series ring `k⟦t⟧`. -/
def specPowerSeries (k : Type u) [CommRing k] : Scheme.{u} :=
  Spec (CommRingCat.of (PowerSeries k))

/-- Unfolding `specPowerSeries` recovers `Spec` of the power series ring. -/
theorem specPowerSeries_eq (k : Type u) [CommRing k] :
    specPowerSeries k = Spec (CommRingCat.of (PowerSeries k)) := rfl

/-- The spectrum of the formal power series ring over a field is locally Noetherian. -/
instance instIsLocallyNoetherianSpecPowerSeries {k : Type u} [Field k] :
    IsLocallyNoetherian (specPowerSeries k) :=
  inferInstanceAs (IsLocallyNoetherian (Spec (CommRingCat.of (PowerSeries k))))

/-- The constant abelian scheme `A = A₀ ×_{Spec k} Spec(k⟦t⟧)` associated to an
abelian variety `A₀` over `k`. -/
def constantAbelianScheme {k : Type u} [Field k] (A0 : SchemeOverField k) [GrpObj A0] :
    GroupScheme (specPowerSeries k) :=
  GroupScheme.baseChange (Grp.mk A0)
    (Spec.map (CommRingCat.ofHom (algebraMap k (PowerSeries k))))

/-- The underlying object of `constantAbelianScheme A0` is the pullback of `A0`
along `Spec(k⟦t⟧) ⟶ Spec k`. -/
theorem constantAbelianScheme_X {k : Type u} [Field k]
    (A0 : SchemeOverField k) [GrpObj A0] :
    (constantAbelianScheme A0).X =
      (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap k (PowerSeries k))))).obj A0 :=
  GroupScheme.baseChange_X (Grp.mk A0)
    (Spec.map (CommRingCat.ofHom (algebraMap k (PowerSeries k))))

/-- The special fibre of a scheme over `Spec(k⟦t⟧)`, obtained by pullback along
`Spec k ⟶ Spec(k⟦t⟧)` induced by the constant-coefficient map. -/
def specialFiber {k : Type u} [Field k] (X : Over (specPowerSeries k)) :
    SchemeOverField k :=
  (Over.pullback (Spec.map (CommRingCat.ofHom PowerSeries.constantCoeff))).obj X

/-- Unfolding `specialFiber` recovers pullback along the constant-coefficient
morphism `Spec k ⟶ Spec(k⟦t⟧)`. -/
theorem specialFiber_eq {k : Type u} [Field k] (X : Over (specPowerSeries k)) :
    specialFiber X =
      (Over.pullback (Spec.map (CommRingCat.ofHom PowerSeries.constantCoeff))).obj X :=
  rfl

end AlgebraicGeometry.HomStack
