/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.AssociatedPoints.Purity
public import ReasLib.AlgebraicGeometry.Scheme.Topology.Stalk

/-!
# Purity over spectra of stalks

Purity along a fibre controls relatively associated points lying over the spectrum of a stalk.
-/

@[expose] public section

open CategoryTheory Limits
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules
namespace IsPureAlong

variable {X S : Scheme.{u}}

/-- For an elementary étale neighbourhood `U` of `s`, the relative assassin of a pulled-back
module over the spectrum of the stalk at `U.point` lies in every open containing that fibre. -/
theorem stalkRelativeAssassin_subset (f : X ⟶ S) [Scheme.Hom.FiniteType f]
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType] (s : S)
    (h_pure : F.IsPureAlong f s) (U : Scheme.EtaleNeighborhood S s)
    (hU : U.IsElementary)
    (W : (Limits.pullback f U.toEtale.hom : Scheme).Opens)
    (h_fiber : (Limits.pullback.snd f U.toEtale.hom) ⁻¹' {U.point} ⊆ (W : Set _)) :
    (Limits.pullback.snd f U.toEtale.hom) ⁻¹'
          Set.range (fromSpecStalk U.toEtale.left U.point) ∩
        relativeAssassin (Limits.pullback.snd f U.toEtale.hom)
          ((Scheme.Modules.pullback (Limits.pullback.fst f U.toEtale.hom)).obj F) ⊆
      (W : Set _) := sorry

end IsPureAlong
end AlgebraicGeometry.Scheme.Modules
