/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Extension.Standard.Sheaf
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Ringed

/-!
# Pullback between standard big sites

This module provides the canonical morphism of ringed sites induced by pullback
along a morphism of schemes equipped with the same standard topology.
-/

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.StandardTopology.Big

/-- Pullback along a scheme morphism is a morphism between the corresponding
standard big sites equipped with the same standard topology. -/
theorem pullback_isMorphismOfSites (τ : StandardTopology)
    {S T : Scheme.{u}} (f : T ⟶ S) :
    IsMorphismOfSites (τ.overTopology S) (τ.overTopology T)
      (Over.pullback f) := sorry

/-- The morphism of standard big ringed sites induced by pullback along a
scheme morphism. -/
noncomputable def pullbackRingedHom (τ : StandardTopology)
    {S T : Scheme.{u}} (f : T ⟶ S) :
    RingedSite.Hom (ringedSite τ T) (ringedSite τ S) :=
  @ringedHom S T τ τ f (pullback_isMorphismOfSites τ f)

end AlgebraicGeometry.StandardTopology.Big
