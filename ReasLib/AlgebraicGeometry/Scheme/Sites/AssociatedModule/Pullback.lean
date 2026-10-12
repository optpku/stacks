/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Quasicoherent.Pullback
public import ReasLib.AlgebraicGeometry.Scheme.Sites.AssociatedModule.Functor
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Standard.Module.Quasicoherent.Pullback

/-!
# Pullback compatibility for associated modules

This module compares pullback of quasi-coherent modules on schemes with pullback
of their associated modules on the standard big and small sites.
-/

@[expose] public section

open CategoryTheory
open AlgebraicGeometry.StandardTopology

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.AssociatedModule

variable {S T : Scheme.{u}}

/-- Associated modules on a standard big site commute with pullback of
quasi-coherent modules along a scheme morphism. -/
theorem pullbackCompatibleBig (τ : StandardTopology) (f : T ⟶ S) :
    IsIsomorphic
      (bigFunctor τ S ⋙ Big.QCoh.pullback τ f)
      (Scheme.QCoh.pullback f ⋙ bigFunctor τ T) := sorry

/-- Associated modules on a selected small standard site commute with pullback
of quasi-coherent modules along a scheme morphism. -/
theorem pullbackCompatibleSmall (σ : SmallStandardTopology) (f : T ⟶ S) :
    IsIsomorphic
      (smallFunctor σ S ⋙ SmallStandardTopology.QCoh.pullback σ f)
      (Scheme.QCoh.pullback f ⋙ smallFunctor σ T) := sorry

/-- Objectwise, big-site pullback of an associated quasi-coherent module is
associated to the scheme-theoretic pullback. -/
theorem pullbackCompatibleBigObj (τ : StandardTopology) (f : T ⟶ S)
    (G : Scheme.QCoh S) :
    IsIsomorphic
      ((Big.QCoh.pullback τ f).obj ((bigFunctor τ S).obj G))
      ((bigFunctor τ T).obj ((Scheme.QCoh.pullback f).obj G)) := sorry

/-- Objectwise, small-site pullback of an associated quasi-coherent module is
associated to the scheme-theoretic pullback. -/
theorem pullbackCompatibleSmallObj (σ : SmallStandardTopology) (f : T ⟶ S)
    (G : Scheme.QCoh S) :
    IsIsomorphic
      ((SmallStandardTopology.QCoh.pullback σ f).obj ((smallFunctor σ S).obj G))
      ((smallFunctor σ T).obj ((Scheme.QCoh.pullback f).obj G)) := sorry

end AlgebraicGeometry.Scheme.AssociatedModule
