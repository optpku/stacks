/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.FormalCompletion
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Pushforward.Composition
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.Coherator.HomotopyLimit
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FinitePresentation.Topology

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open RingedSite.Hom.DerivedAdjunction
open RingedSpace.moduleDerivedPushforward.Composition
open Scheme.ModuleDerived.Quasicoherent

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.ModuleDerived.FormalCompletion.System

/-- The quasi-coherent coreflection of an ambient homotopy limit of the
pushforwards in a formal-completion system is bounded above. -/
theorem coheratorHomotopyLimit_isBoundedAbove
    {A : SequentialInverseSystem CommRingCat.{u}} {A_lim : LimitCone A}
    {X : Scheme.{u}} {f : X ⟶ Spec A_lim.cone.pt}
    [IsProper f] [Flat f] [Scheme.Hom.FinitePresentation f]
    {Xn : ℕ → Scheme.{u}} {p : ∀ n, Xn n ⟶ X}
    {q : ∀ n, Xn n ⟶ Spec (A.obj (Opposite.op n))}
    {i : ∀ n, Xn n ⟶ Xn (n + 1)}
    [∀ n, HasPair (RingedSpace.opensRingedSiteHom (i n).toShHom)]
    (S : FormalCompletion.System A A_lim X f Xn p q i)
    [∀ n, HasPair (RingedSpace.opensRingedSiteHom (p n).toShHom)]
    [∀ n, HasPair (RingedSpace.opensRingedSiteHom
      ((i n).toShHom ≫ (p (n + 1)).toShHom))]
    (Ksys : SequentialInverseSystem (RingedSpace.ModuleDerived X.toRingedSpace))
    (stageIso : ∀ n, Ksys.obj (Opposite.op n) ≅
      (RingedSpace.moduleDerivedPushforward (p n).toShHom).obj (S.K n))
    (stageIso_naturality : ∀ n,
      Ksys.stepMap n ≫ (stageIso n).hom =
        (stageIso (n + 1)).hom ≫
          (RingedSpace.moduleDerivedPushforward (p (n + 1)).toShHom).map (S.φ n) ≫
          (iso
            (i n).toShHom (p (n + 1)).toShHom
            (RingedSpace.modulePullbackDerived.compComparison_isIso
              (i n).toShHom (p (n + 1)).toShHom)).hom.app (S.K n) ≫
          eqToHom (congrArg
            (fun g ↦ (RingedSpace.moduleDerivedPushforward g).obj (S.K n))
            ((LocallyRingedSpace.comp_toShHom
              (i n).toLRSHom (p (n + 1)).toLRSHom).symm.trans
                ((congrArg (fun g ↦ g.toShHom)
                  (Scheme.Hom.comp_toLRSHom (i n) (p (n + 1)))).symm.trans
                    (congrArg (fun g : Xn n ⟶ X ↦ g.toShHom) (S.comp_p n))))))
    (Klim : RingedSpace.ModuleDerived X.toRingedSpace)
    (hKlim : HomotopyLimit.IsOf Ksys Klim) :
    DerivedCategory.IsBoundedAbove
      ((@Functor.rightAdjoint _ _ _ _ (Scheme.DerivedQCoh.inclusion X)
        (@Scheme.DerivedQCoh.inclusionIsLeftAdjoint X
          (Scheme.Hom.compactSpace_of_finitePresentation f)
          (Scheme.Hom.quasiSeparatedSpace_of_finitePresentation f))).obj Klim).obj := sorry

end AlgebraicGeometry.Scheme.ModuleDerived.FormalCompletion.System
