/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.Resolution.Hom
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Localization.Homology
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 21.34.6

The statement is already available at its reusable level for arbitrary abelian categories and
bundled ringed sites.  Chosen isomorphisms `Q.obj L ≅ K` and `Q.obj I ≅ M` express precisely that
the complexes represent the derived objects; no commutative-ring presentation or proof-local
derived-category instance is part of the API.
-/

/- Lemma 21.34.6 (1) (0A94): after restriction to any object of a ringed site, degree-zero
Hom-complex cohomology computes morphisms between the represented localized derived objects. -/
@[stacks 0A94 "localized K-injective Hom comparison"] #check
  @RingedSite.Hom.LocalizedRestriction.Homology.zeroAddEquivOfIso

/- Lemma 21.34.6 (2) (0A94): globally, degree-zero Hom-complex cohomology computes morphisms
between the represented derived objects. -/
@[stacks 0A94 "ambient K-injective Hom comparison"] #check
  @CochainComplex.Resolution.injectiveHomologyZeroAddEquivOfIso
