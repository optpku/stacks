/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.FormalCompletion.PseudoCoherent
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.FormalCompletion.OpenSections

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open RingedSite.Hom.DerivedAdjunction

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.ModuleDerived.FormalCompletion.System

/-- A compatible system of pseudo-coherent derived modules on successive locally
nilpotent thickenings algebraizes to a pseudo-coherent derived module on the ambient
scheme, compatibly with all transition maps. -/
@[stacks 0DIG]
theorem exists_pseudoCoherent_of_thickenings
    {A : SequentialInverseSystem CommRingCat.{u}} {A_lim : LimitCone A}
    {X : Scheme.{u}} {f : X ⟶ Spec A_lim.cone.pt}
    [IsProper f] [Flat f] [Scheme.Hom.FinitePresentation f]
    {Xn : ℕ → Scheme.{u}} {p : ∀ n, Xn n ⟶ X}
    {q : ∀ n, Xn n ⟶ Spec (A.obj (Opposite.op n))}
    {i : ∀ n, Xn n ⟶ Xn (n + 1)}
    [∀ n, HasPair (RingedSpace.opensRingedSiteHom (i n).toShHom)]
    (S : FormalCompletion.System A A_lim X f Xn p q i) :
    ∃ (K : RingedSpace.ModuleDerived X.toRingedSpace)
      (e : ∀ n, (RingedSpace.modulePullbackDerived (p n).toShHom).obj K ≅ S.K n),
      RingedSpace.ModuleDerived.IsPseudoCoherent K ∧
        ∀ n,
          (RingedSpace.modulePullbackDerived (i n).toShHom).map (e (n + 1)).hom ≫
              S.pullbackTransition n =
            (RingedSpace.modulePullbackDerived.compComparison
                (i n).toShHom (p (n + 1)).toShHom).app K ≫
              eqToHom (congrArg
                (fun g ↦ (RingedSpace.modulePullbackDerived g).obj K)
                ((LocallyRingedSpace.comp_toShHom
                  (i n).toLRSHom (p (n + 1)).toLRSHom).symm.trans
                    ((congrArg (fun g ↦ g.toShHom)
                      (Scheme.Hom.comp_toLRSHom (i n) (p (n + 1)))).symm.trans
                        (congrArg (fun g : Xn n ⟶ X ↦ g.toShHom) (S.comp_p n))))) ≫
              (e n).hom := sorry

end AlgebraicGeometry.Scheme.ModuleDerived.FormalCompletion.System
