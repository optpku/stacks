/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.DeRham
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Differentials.Stalk
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Ideal.Stalk.Generator
public import ReasLib.AlgebraicGeometry.Scheme.Divisor.EffectiveCartier

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.DeRham.LogPole

/-- Multiplication by the relative differential of a local equation in the canonical
Kähler-differential model of the relative-differentials stalk. -/
noncomputable def differentialSpan {S X : Scheme.{u}} (f : X ⟶ S)
    (x : X) (a : X.presheaf.stalk x) :
    ModuleCat.of (X.presheaf.stalk x) (X.presheaf.stalk x) ⟶
      TopCat.Sheaf.RelativeDifferentials.Stalk.target
        (RingedSpace.DeRham.structureMap f.toLRSHom.toShHom) x :=
  @ModuleCat.ofHom (X.presheaf.stalk x) inferInstance
    (X.presheaf.stalk x)
    (TopCat.Sheaf.RelativeDifferentials.Stalk.target
      (RingedSpace.DeRham.structureMap f.toLRSHom.toShHom) x)
    inferInstance inferInstance inferInstance (ModuleCat.isModule _)
    (@LinearMap.toSpanSingleton (X.presheaf.stalk x)
      (TopCat.Sheaf.RelativeDifferentials.Stalk.target
        (RingedSpace.DeRham.structureMap f.toLRSHom.toShHom) x)
      inferInstance inferInstance (ModuleCat.isModule _)
      (CommRingCat.KaehlerDifferential.d a))

/-- The stalk map determined by a local equation is the span map of its universal differential. -/
theorem differentialSpan_def {S X : Scheme.{u}} (f : X ⟶ S)
    (x : X) (a : X.presheaf.stalk x) :
    differentialSpan f x a =
      @ModuleCat.ofHom (X.presheaf.stalk x) inferInstance
        (X.presheaf.stalk x)
        (TopCat.Sheaf.RelativeDifferentials.Stalk.target
          (RingedSpace.DeRham.structureMap f.toLRSHom.toShHom) x)
        inferInstance inferInstance inferInstance (ModuleCat.isModule _)
        (@LinearMap.toSpanSingleton (X.presheaf.stalk x)
          (TopCat.Sheaf.RelativeDifferentials.Stalk.target
            (RingedSpace.DeRham.structureMap f.toLRSHom.toShHom) x)
          inferInstance inferInstance (ModuleCat.isModule _)
          (CommRingCat.KaehlerDifferential.d a)) := sorry

/-- The de Rham complex with logarithmic poles along `i` is defined when multiplication by
`da` is split injective for every stalkwise local equation `a`, and every relative form sheaf
is free of torsion by such local equations. -/
structure IsDefined {S X Y : Scheme.{u}} (f : X ⟶ S) (i : Y ⟶ X)
    [IsEffectiveCartierDivisor i] : Prop where
  /-- For every local equation `a`, the stalk map `g ↦ g • da` is split injective. -/
  differential_split :
    ∀ (y : Y) (a : X.presheaf.stalk (i.base y)),
      RingedSpace.IdealSheaf.IsStalkGenerator
          (RingedSpace.Hom.idealSheafSubobject i.toShHom) (i.base y) a →
        IsSplitMono (differentialSpan f (i.base y) a)
  /-- Every relative differential-form sheaf is torsion-free for local equations of `Y`. -/
  form_torsionFree :
    ∀ (p : ℕ) (y : Y) (a : X.presheaf.stalk (i.base y)),
      RingedSpace.IdealSheaf.IsStalkGenerator
          (RingedSpace.Hom.idealSheafSubobject i.toShHom) (i.base y) a →
        IsSMulRegular
          (RingedSpace.stalkModuleCat (RingedSpace.DeRham.form f.toLRSHom.toShHom p)
            (i.base y)) a

namespace IsDefined

/-- Build the log-pole definability condition from its two stalkwise clauses. -/
def ofStalkConditions {S X Y : Scheme.{u}} (f : X ⟶ S) (i : Y ⟶ X)
    [IsEffectiveCartierDivisor i]
    (h_split : ∀ (y : Y) (a : X.presheaf.stalk (i.base y)),
      RingedSpace.IdealSheaf.IsStalkGenerator
          (RingedSpace.Hom.idealSheafSubobject i.toShHom) (i.base y) a →
        IsSplitMono (differentialSpan f (i.base y) a))
    (h_torsionFree : ∀ (p : ℕ) (y : Y) (a : X.presheaf.stalk (i.base y)),
      RingedSpace.IdealSheaf.IsStalkGenerator
          (RingedSpace.Hom.idealSheafSubobject i.toShHom) (i.base y) a →
        IsSMulRegular
          (RingedSpace.stalkModuleCat (RingedSpace.DeRham.form f.toLRSHom.toShHom p)
            (i.base y)) a) :
    IsDefined f i where
  differential_split := h_split
  form_torsionFree := h_torsionFree

/-- The log-pole definability condition is exactly its split-differential and torsion-free
stalkwise clauses. -/
theorem iff_stalkConditions {S X Y : Scheme.{u}} (f : X ⟶ S) (i : Y ⟶ X)
    [IsEffectiveCartierDivisor i] :
    IsDefined f i ↔
      (∀ (y : Y) (a : X.presheaf.stalk (i.base y)),
        RingedSpace.IdealSheaf.IsStalkGenerator
            (RingedSpace.Hom.idealSheafSubobject i.toShHom) (i.base y) a →
          IsSplitMono (differentialSpan f (i.base y) a)) ∧
      ∀ (p : ℕ) (y : Y) (a : X.presheaf.stalk (i.base y)),
        RingedSpace.IdealSheaf.IsStalkGenerator
            (RingedSpace.Hom.idealSheafSubobject i.toShHom) (i.base y) a →
          IsSMulRegular
            (RingedSpace.stalkModuleCat (RingedSpace.DeRham.form f.toLRSHom.toShHom p)
              (i.base y)) a := sorry

end IsDefined

end AlgebraicGeometry.RingedSpace.DeRham.LogPole
