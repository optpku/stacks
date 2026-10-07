module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.PseudoCoherent.Relative.Algebraization

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open RingedSite.Hom.DerivedAdjunction

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.ModuleDerived

variable (A : SequentialInverseSystem CommRingCat.{u})
variable (A_lim : LimitCone A)
variable (h_surjective : A.Surjective)
variable (h_kernel : A.KernelLocallyNilpotent)

variable (X : Scheme.{u}) (f : X ⟶ Spec A_lim.cone.pt)
variable [IsSeparated f] [Scheme.Hom.FinitePresentation f]

variable (Xn : ℕ → Scheme.{u})
variable (p : ∀ n, Xn n ⟶ X)
variable (q : ∀ n, Xn n ⟶ Spec (A.obj (Opposite.op n)))
variable (h_pullback : ∀ n,
  IsPullback (q n) (p n) (Spec.map (A_lim.cone.stageMap n)) f)
variable (h_closed : ∀ n, IsClosedImmersion (p n))

variable (i : ∀ n, Xn n ⟶ Xn (n + 1))
variable (hiX : ∀ n, i n ≫ p (n + 1) = p n)
variable (hiA : ∀ n,
  i n ≫ q (n + 1) = q n ≫ Spec.map (A.stepMap n))

variable (Kn : ∀ n, RingedSpace.ModuleDerived (Xn n).toRingedSpace)
variable (h_pseudoCoherent : ∀ n,
  @IsPseudoCoherentOver _ _ (q n)
    (MorphismProperty.of_isPullback (P := @LocallyOfFiniteType)
      (h_pullback n).flip (inferInstanceAs (LocallyOfFiniteType f))) (Kn n))
variable (h_support : ∀ n, ∃ Z : TopologicalSpace.Closeds (Xn n),
  ClosedSubset.IsProperOver (q n) Z ∧
    RingedSpace.ModuleDerived.IsSupportedOn (Kn n) (Z : Set (Xn n)))
variable [∀ n, HasPair (RingedSpace.opensRingedSiteHom (i n).toShHom)]
variable (φ : ∀ n, Kn (n + 1) ⟶
  (RingedSpace.moduleDerivedPushforward (i n).toShHom).obj (Kn n))
variable (hφ : ∀ n, IsIso
  (((RingedSpace.modulePullbackDerivedPushforwardAdjunction (i n).toShHom).homEquiv
    (Kn (n + 1)) (Kn n)).symm (φ n)))

/- Remark 38.29.7: a compatible system of relatively pseudo-coherent complexes with proper
support on the thickenings algebraizes to a relatively pseudo-coherent complex with proper
support over the limit, compatibly with the transition maps. -/
@[stacks 0DIH] #check
  (AlgebraicGeometry.Scheme.ModuleDerived.exists_pseudoCoherentOver_withProperSupport_of_thickenings
      A A_lim h_surjective h_kernel X f Xn p q h_pullback h_closed i hiX hiA Kn
        h_pseudoCoherent h_support φ hφ :
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
              (e n).hom)

end AlgebraicGeometry.Scheme.ModuleDerived
