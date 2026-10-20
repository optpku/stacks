/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Chow.Qcqs

/-!
# Chow's lemma for schemes with finitely many irreducible components

This file states the quasi-compact, quasi-separated form of Chow's lemma with an isomorphism over
a dense open when the source has finitely many irreducible components.
-/

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.ChowLemmaModification

/-- A separated finite-type morphism from a scheme with finitely many irreducible components to
a quasi-compact, quasi-separated scheme admits a Chow modification that is an isomorphism over a
dense open of its target. -/
theorem exists_of_separated_finiteType_of_finite_irreducibleComponents
    {X S : Scheme.{u}} (f : X ⟶ S) [CompactSpace S] [QuasiSeparatedSpace S]
    [IsSeparated f] [Scheme.Hom.FiniteType f] [Finite (irreducibleComponents X)] :
    Nonempty (ChowLemmaModification f) := sorry

end AlgebraicGeometry.ChowLemmaModification
