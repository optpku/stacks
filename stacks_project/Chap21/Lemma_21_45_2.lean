/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.PseudoCoherent.Local
import StacksCheckRecall

@[expose] public section

/- Lemma 21.45.2 (1) (08FU): a strict-perfect approximation on a cover of a terminal object
implies `m`-pseudo-coherence. -/
@[stacks 08FU "(1)"]
#check @RingedSite.DerivedCategory.isMPseudoCoherent_of_cover_of_isTerminal

/- Lemma 21.45.2 (2) (08FU): every complex representing an `m`-pseudo-coherent derived module
is `m`-pseudo-coherent. -/
@[stacks 08FU "(2)"]
#check @RingedSite.Hom.ModuleDerived.IsMPseudoCoherent.of_representation

/- Lemma 21.45.2 (3) (08FU): `m`-pseudo-coherence descends from covering families of local
restrictions. -/
@[stacks 08FU "(3)"]
#check @RingedSite.DerivedCategory.isMPseudoCoherent_of_locally_isMPseudoCoherent

#check @RingedSite.DerivedCategory.HasStrictlyPerfectApproximationInDegree
#check @RingedSite.DerivedCategory.isMPseudoCoherent_iff_forall_hasStrictlyPerfectApproximationInDegree
