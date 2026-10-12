/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.CommRingCat.InverseSystem
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Adjunction
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Pullback.Composition
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Support
public import ReasLib.AlgebraicGeometry.Scheme.ClosedSubscheme.Proper
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.PseudoCoherent.Relative
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.Tactic.CrossRefAttribute

/-!
# Algebraization of relatively pseudo-coherent derived modules

Compatible relatively pseudo-coherent derived modules with proper support over a system of
nilpotent thickenings algebraize over the inverse limit.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open RingedSite.Hom.DerivedAdjunction

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.ModuleDerived

/-- A compatible system of relatively pseudo-coherent derived modules with proper support over
successive locally nilpotent thickenings algebraizes to a relatively pseudo-coherent derived
module with proper support over the inverse limit, compatibly with all transition maps. -/
@[stacks 0DIH]
theorem exists_pseudoCoherentOver_withProperSupport_of_thickenings
    (A : SequentialInverseSystem CommRingCat.{u}) (A_lim : LimitCone A)
    (h_surjective : A.Surjective) (h_kernel : A.KernelLocallyNilpotent)
    (X : Scheme.{u}) (f : X ⟶ Spec A_lim.cone.pt)
    [IsSeparated f] [Scheme.Hom.FinitePresentation f]
    (Xn : ℕ → Scheme.{u}) (p : ∀ n, Xn n ⟶ X)
    (q : ∀ n, Xn n ⟶ Spec (A.obj (Opposite.op n)))
    (h_pullback : ∀ n,
      IsPullback (q n) (p n) (Spec.map (A_lim.cone.stageMap n)) f)
    (h_closed : ∀ n, IsClosedImmersion (p n))
    (i : ∀ n, Xn n ⟶ Xn (n + 1))
    (hiX : ∀ n, i n ≫ p (n + 1) = p n)
    (hiA : ∀ n, i n ≫ q (n + 1) = q n ≫ Spec.map (A.stepMap n))
    (Kn : ∀ n, RingedSpace.ModuleDerived (Xn n).toRingedSpace)
    (h_pseudoCoherent : ∀ n,
      @IsPseudoCoherentOver _ _ (q n)
        (MorphismProperty.of_isPullback (P := @LocallyOfFiniteType)
          (h_pullback n).flip (inferInstanceAs (LocallyOfFiniteType f))) (Kn n))
    (h_support : ∀ n, ∃ Z : TopologicalSpace.Closeds (Xn n),
      ClosedSubset.IsProperOver (q n) Z ∧
        RingedSpace.ModuleDerived.IsSupportedOn (Kn n) (Z : Set (Xn n)))
    [∀ n, HasPair (RingedSpace.opensRingedSiteHom (i n).toShHom)]
    (φ : ∀ n, Kn (n + 1) ⟶
      (RingedSpace.moduleDerivedPushforward (i n).toShHom).obj (Kn n))
    (hφ : ∀ n, IsIso
      (((RingedSpace.modulePullbackDerivedPushforwardAdjunction
        (i n).toShHom).homEquiv (Kn (n + 1)) (Kn n)).symm (φ n))) :
    ∃ (K : RingedSpace.ModuleDerived X.toRingedSpace)
      (e : ∀ n, (RingedSpace.modulePullbackDerived (p n).toShHom).obj K ≅ Kn n),
      IsPseudoCoherentOver f K ∧
        (∃ Z : TopologicalSpace.Closeds X,
          ClosedSubset.IsProperOver f Z ∧
            RingedSpace.ModuleDerived.IsSupportedOn K (Z : Set X)) ∧
        ∀ n,
          (RingedSpace.modulePullbackDerived (i n).toShHom).map (e (n + 1)).hom ≫
              ((RingedSpace.modulePullbackDerivedPushforwardAdjunction
                (i n).toShHom).homEquiv (Kn (n + 1)) (Kn n)).symm (φ n) =
            (RingedSpace.modulePullbackDerived.compComparison
                (i n).toShHom (p (n + 1)).toShHom).app K ≫
              eqToHom (congrArg
                (fun g ↦ (RingedSpace.modulePullbackDerived g).obj K)
                ((LocallyRingedSpace.comp_toShHom
                  (i n).toLRSHom (p (n + 1)).toLRSHom).symm.trans
                    ((congrArg (fun g ↦ g.toShHom)
                      (Scheme.Hom.comp_toLRSHom (i n) (p (n + 1)))).symm.trans
                        (congrArg (fun g : Xn n ⟶ X ↦ g.toShHom) (hiX n))))) ≫
              (e n).hom := sorry

end AlgebraicGeometry.Scheme.ModuleDerived
