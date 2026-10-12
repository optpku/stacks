/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Pushforward.Leray
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 21.14.5

The reusable owner is `RingedSite.Hom.Leray`, the canonical Grothendieck spectral sequence for
module direct image followed by global sections.  Its generic page and abutment are canonical;
the textbook expressions are exposed separately by `Leray.Ext.pageTwo_isIsomorphic` and
`Leray.abutment_isIsomorphic`.

The lower-level `Leray.nonemptyOfAcyclic` retains the abstract Grothendieck hypothesis.  For a
`RingedSite.Hom`, `Leray.isAcyclic` derives it from the reusable 072Z acyclicity owner, so the
source-facing theorem does not expose an auxiliary hypothesis.
-/

/- Lemma 21.14.5 (0732): for a morphism `f` and a bounded-below derived module `K`, the Leray
spectral sequence exists. -/
@[stacks 0732] #check @RingedSite.Hom.Leray.nonempty

-- Its `(p, q)` second-page object is the textbook `Ext^p(𝒪_Y, H^q(Rf_*K))`.
#check @RingedSite.Hom.Leray.Ext.pageTwo_isIsomorphic

-- Its degree-`n` abutment is derived global cohomology of `K` on the source.
#check @RingedSite.Hom.Leray.abutment_isIsomorphic

-- The shared realization also exposes maps over derived morphisms for downstream arguments.
#check @RingedSite.Hom.Leray.existsMap

end
