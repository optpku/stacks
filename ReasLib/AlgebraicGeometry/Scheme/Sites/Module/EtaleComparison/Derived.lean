/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Comparison
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Module.EtaleComparison

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry
open AlgebraicGeometry.StandardTopology
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.Etale
open RingedSite.Hom

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale.ModuleComparison

/-- The right-derived direct image along fppf restriction exists for lifted module sheaves. -/
instance restrictionHasRightDerived (S : Scheme.{u}) :
    Functor.HasRightDerivedFunctor
      (modulePushforwardToDerived.{u+1}
        (SiteRestriction.bigToEtale .fppf S (fun h ↦ nomatch h)))
      (ModuleQis.{u+1} (Big.ringedSite .fppf S)) :=
  modulePushforwardToDerived.hasRightDerived.{u+1}
    (SiteRestriction.bigToEtale .fppf S (fun h ↦ nomatch h))

/-- The right-derived direct image along the big topology comparison exists for lifted modules. -/
instance topologyHasRightDerived (S : Scheme.{u}) :
    Functor.HasRightDerivedFunctor
      (modulePushforwardToDerived.{u+1} (Big.toFppfHom .etale S))
      (ModuleQis.{u+1} (Big.ringedSite .fppf S)) :=
  modulePushforwardToDerived.hasRightDerived.{u+1} (Big.toFppfHom .etale S)

/-- The ordinary topology comparison from the étale pullback to the fppf direct image. -/
def ordinaryTopologyUnit (S : Scheme.{u})
    (F : RingedSite.ModuleCat.{u} (Small.ringedSite S)) [F.IsQuasicoherent] :
    (SiteRestriction.bigToEtale .etale S (fun h ↦ nomatch h)).modulePullback.{u+1}.obj
        (RingedSite.Module.carrierLift (Small.ringedSite S) F) ⟶
      (Big.toFppfHom .etale S).modulePushforward.{u+1}.obj
        ((SiteRestriction.bigToEtale .fppf S (fun h ↦ nomatch h)).modulePullback.{u+1}.obj
          (RingedSite.Module.carrierLift (Small.ringedSite S) F)) :=
  ((modulePullbackPushforwardAdjunction.{u+1}
    (SiteRestriction.bigToEtale .etale S (fun h ↦ nomatch h))).homEquiv _ _).symm
      ((modulePullbackPushforwardAdjunction.{u+1}
        (SiteRestriction.bigToEtale .fppf S (fun h ↦ nomatch h))).unit.app
          (RingedSite.Module.carrierLift (Small.ringedSite S) F))

/-- The ordinary topology comparison satisfies the adjunction-unit identity. -/
theorem ordinaryTopologyUnit_unit (S : Scheme.{u})
    (F : RingedSite.ModuleCat.{u} (Small.ringedSite S)) [F.IsQuasicoherent] :
    (modulePullbackPushforwardAdjunction.{u+1}
        (SiteRestriction.bigToEtale .etale S (fun h ↦ nomatch h))).unit.app
      (RingedSite.Module.carrierLift (Small.ringedSite S) F) ≫
        (SiteRestriction.bigToEtale .etale S (fun h ↦ nomatch h)).modulePushforward.{u+1}.map
          (ordinaryTopologyUnit S F) =
    (modulePullbackPushforwardAdjunction.{u+1}
      (SiteRestriction.bigToEtale .fppf S (fun h ↦ nomatch h))).unit.app
        (RingedSite.Module.carrierLift (Small.ringedSite S) F) := by
  exact ((modulePullbackPushforwardAdjunction.{u+1}
    (SiteRestriction.bigToEtale .etale S (fun h ↦ nomatch h))).homEquiv _ _).apply_symm_apply _

/-- The first canonical comparison from ordinary étale pullback to derived fppf direct image. -/
def topologyComparison (S : Scheme.{u})
    (F : RingedSite.ModuleCat.{u} (Small.ringedSite S)) [F.IsQuasicoherent] :=
  RingedSite.Hom.ordinaryToRightDerived (Big.toFppfHom .etale S)
    ((SiteRestriction.bigToEtale .fppf S (fun h ↦ nomatch h)).modulePullback.{u+1}.obj
      (RingedSite.Module.carrierLift (Small.ringedSite S) F))
    ((SiteRestriction.bigToEtale .etale S (fun h ↦ nomatch h)).modulePullback.{u+1}.obj
      (RingedSite.Module.carrierLift (Small.ringedSite S) F))
    (ordinaryTopologyUnit S F)

/-- The second canonical comparison from the original module to derived fppf direct image. -/
def restrictionComparison (S : Scheme.{u})
    (F : RingedSite.ModuleCat.{u} (Small.ringedSite S)) [F.IsQuasicoherent] :=
  RingedSite.Hom.ordinaryToRightDerived
    (SiteRestriction.bigToEtale .fppf S (fun h ↦ nomatch h))
    ((SiteRestriction.bigToEtale .fppf S (fun h ↦ nomatch h)).modulePullback.{u+1}.obj
      (RingedSite.Module.carrierLift (Small.ringedSite S) F))
    (RingedSite.Module.carrierLift (Small.ringedSite S) F)
    ((modulePullbackPushforwardAdjunction.{u+1}
      (SiteRestriction.bigToEtale .fppf S (fun h ↦ nomatch h))).unit.app
        (RingedSite.Module.carrierLift (Small.ringedSite S) F))

/-- The ordinary étale-to-fppf derived comparison is an isomorphism. -/
theorem topologyComparison_isIso
    (S : Scheme.{u}) (F : RingedSite.ModuleCat.{u} (Small.ringedSite S))
    [F.IsQuasicoherent] : IsIso (topologyComparison S F) := sorry

/-- The ordinary restriction-to-fppf derived comparison is an isomorphism. -/
theorem restrictionComparison_isIso
    (S : Scheme.{u}) (F : RingedSite.ModuleCat.{u} (Small.ringedSite S))
    [F.IsQuasicoherent] : IsIso (restrictionComparison S F) := sorry

end AlgebraicGeometry.Scheme.Etale.ModuleComparison

