/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.DeRham.LogPole
public import ReasLib.AlgebraicGeometry.RingedSpace.DeRham.Map
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Differentials.Stalk
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Ideal.Stalk.Generator
public import ReasLib.AlgebraicGeometry.Scheme.Divisor.EffectiveCartier

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.DeRham.LogPole

/- The promoted declarations remain available through this compatibility module. -/
#check (AlgebraicGeometry.RingedSpace.DeRham.LogPole.differentialSpan :
  ∀ {S X : Scheme.{u}} (f : X ⟶ S) (x : X) (a : X.presheaf.stalk x),
    ModuleCat.of (X.presheaf.stalk x) (X.presheaf.stalk x) ⟶
      TopCat.Sheaf.RelativeDifferentials.Stalk.target
        (RingedSpace.DeRham.structureMap f.toLRSHom.toShHom) x)
#check (AlgebraicGeometry.RingedSpace.DeRham.LogPole.differentialSpan_def :
  ∀ {S X : Scheme.{u}} (f : X ⟶ S) (x : X) (a : X.presheaf.stalk x),
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
          (CommRingCat.KaehlerDifferential.d a)))
#check (@AlgebraicGeometry.RingedSpace.DeRham.LogPole.IsDefined :
  {S X Y : Scheme.{u}} → (X ⟶ S) → (i : Y ⟶ X) →
    [AlgebraicGeometry.IsEffectiveCartierDivisor i] → Prop)
#check (AlgebraicGeometry.RingedSpace.DeRham.LogPole.IsDefined.ofStalkConditions :
  ∀ {S X Y : Scheme.{u}} (f : X ⟶ S) (i : Y ⟶ X)
    [IsEffectiveCartierDivisor i],
    (∀ (y : Y) (a : X.presheaf.stalk (i.base y)),
      RingedSpace.IdealSheaf.IsStalkGenerator
          (RingedSpace.Hom.idealSheafSubobject i.toShHom) (i.base y) a →
        IsSplitMono (differentialSpan f (i.base y) a)) →
    (∀ (p : ℕ) (y : Y) (a : X.presheaf.stalk (i.base y)),
      RingedSpace.IdealSheaf.IsStalkGenerator
          (RingedSpace.Hom.idealSheafSubobject i.toShHom) (i.base y) a →
        IsSMulRegular
          (RingedSpace.stalkModuleCat (RingedSpace.DeRham.form f.toLRSHom.toShHom p)
            (i.base y)) a) →
    IsDefined f i)
#check (AlgebraicGeometry.RingedSpace.DeRham.LogPole.IsDefined.iff_stalkConditions :
  ∀ {S X Y : Scheme.{u}} (f : X ⟶ S) (i : Y ⟶ X)
    [IsEffectiveCartierDivisor i],
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
              (i.base y)) a)

end AlgebraicGeometry.RingedSpace.DeRham.LogPole
