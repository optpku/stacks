/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Localization.InternalHom
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 21.35.3

Localized restriction preserves the derived internal Hom through the canonical oplax-monoidal
comparison owned by ReasLib.  The chapter statement is a source-facing recall of that owner and
does not rebuild a pullback comparison or local derived-category instances.
-/

/- Lemma 21.35.3 (08JB): the localized restriction/internal-Hom comparison. -/
@[stacks 08JB "localized restriction and derived internal Hom"] #check
  @RingedSite.Hom.LocalizedRestriction.InternalHom.comparison

/- Lemma 21.35.3 (08JB): the comparison is an isomorphism. -/
@[stacks 08JB "localized restriction preserves derived internal Hom"] #check
  @RingedSite.Hom.LocalizedRestriction.InternalHom.comparison_isIso
