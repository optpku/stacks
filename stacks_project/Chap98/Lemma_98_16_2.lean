/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Artin
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry Limits Opposite
universe u

namespace AlgebraicGeometry.AlgebraicSpace

open Scheme.Over

/- Lemma 98.16.2. A presheaf satisfying Artin's axioms [0], [1], [2], [4], and [5]
over a locally Noetherian scheme with G-ring stalks at finite-type points is an
algebraic space if it admits a monomorphism into an algebraic space locally of
finite type over the base. -/
@[stacks 07Y2] #check (AlgebraicGeometry.AlgebraicSpace.IsAlgebraicSpace.of_mono :
    ∀ {S : Scheme.{u}} [IsLocallyNoetherian S]
    {F : (Over S)ᵒᵖ ⥤ Type u} {G : AlgebraicSpace S}
    (a : F ⟶ G.functorOfPoints) [Mono a]
    [LocallyOfFiniteType (SchemeRealization.toBase G)]
    (h0 : Presheaf.IsSheaf (Scheme.etaleTopology.over S) F)
    (h1 : PreservesDirectedAffineLimits S F)
    (hRS : GroupoidsOver.HasRimSchlessinger (toGroupoidsOver F))
    (h_eff : ∀ ξ : GroupoidsOver.FormalObject (toGroupoidsOver F),
      GroupoidsOver.FormalObject.IsEffective ξ)
    (h_open : GroupoidsOver.OpennessOfVersality (toGroupoidsOver F))
    (hG : ∀ s : S, IsFiniteTypePoint s → IsGRing (S.presheaf.stalk s)),
    IsAlgebraicSpace F)

end AlgebraicGeometry.AlgebraicSpace
