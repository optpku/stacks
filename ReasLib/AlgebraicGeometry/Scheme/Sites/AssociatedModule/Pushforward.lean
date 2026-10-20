module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.AssociatedModule.Functor
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Standard.Module.Quasicoherent.Pushforward
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Standard.Pullback

/-!
# Pushforward compatibility for associated modules

This module compares pushforward of quasi-coherent modules on schemes with
pushforward of their associated modules on standard sites.
-/

@[expose] public section

open CategoryTheory
open AlgebraicGeometry.StandardTopology

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.AssociatedModule

variable {S T : Scheme.{u}}

/-- For every standard big topology, big-site pushforward is not universally
compatible with qcqs scheme-theoretic pushforward. -/
theorem notBigPushforwardCompatible (τ : StandardTopology) :
    ¬ ∀ (S T : Scheme.{u}) (f : T ⟶ S) [QuasiCompact f] [QuasiSeparated f],
      IsIsomorphic
        (bigFunctor τ T ⋙
          (SheafOfModules.isQuasicoherent (bigStructureSheaf τ T)).ι ⋙
          (StandardTopology.Big.pullbackRingedHom τ f).modulePushforward)
        (Scheme.QCoh.pushforward f ⋙ bigFunctor τ S ⋙
          (SheafOfModules.isQuasicoherent (bigStructureSheaf τ S)).ι) := sorry

/-- Along a qcqs scheme morphism, associated modules on a selected small
standard site commute with pushforward. -/
theorem smallPushforwardCompatible (σ : SmallStandardTopology)
    (f : T ⟶ S) [QuasiCompact f] [QuasiSeparated f] :
    IsIsomorphic
      (smallFunctor σ T ⋙ SmallStandardTopology.QCoh.pushforward σ f)
      (Scheme.QCoh.pushforward f ⋙ smallFunctor σ S) := sorry

/-- Objectwise, small-site pushforward of an associated quasi-coherent module
is associated to the scheme-theoretic pushforward. -/
theorem smallPushforwardCompatibleObj (σ : SmallStandardTopology)
    (f : T ⟶ S) [QuasiCompact f] [QuasiSeparated f] (F : Scheme.QCoh T) :
    IsIsomorphic
      ((SmallStandardTopology.QCoh.pushforward σ f).obj ((smallFunctor σ T).obj F))
      ((smallFunctor σ S).obj ((Scheme.QCoh.pushforward f).obj F)) := sorry

end AlgebraicGeometry.Scheme.AssociatedModule
