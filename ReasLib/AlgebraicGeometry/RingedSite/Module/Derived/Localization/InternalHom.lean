/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Localization
public import ReasLib.CategoryTheory.Monoidal.Closed.OplaxMonoidal
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Internal Hom and localized restriction

This file owns the derived internal-Hom comparison for restriction to a localized ringed site.
The comparison is inherited from the generic oplax-monoidal internal-Hom construction, with its
coherence supplied by the monoidal restriction functor.  The `IsIso` instance records the
additional localization theorem and is intentionally attached to this canonical functor rather
than to a chapter file.
-/

open CategoryTheory
open CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed

noncomputable section

universe u v w z

namespace RingedSite.Hom.LocalizedRestriction.InternalHom

variable (X : RingedSite.{u, v, w}) (U : X)
variable [UnivLE.{max u v, z}]

variable [MonoidalCategory (ModuleDerived.{z} X)]
variable [BraidedCategory (ModuleDerived.{z} X)]
variable [MonoidalClosed (ModuleDerived.{z} X)]
variable [MonoidalCategory (ModuleDerived.{z} (X.localization U))]
variable [BraidedCategory (ModuleDerived.{z} (X.localization U))]
variable [MonoidalClosed (ModuleDerived.{z} (X.localization U))]
variable [Functor.Monoidal (localizedRestrictionDerived.{z} X U)]

/-- Lemma 20.42.3 (08DL): the canonical map from the derived internal Hom on a ringed site to
the internal Hom after restriction to `X.localization U`.

The tensor comparison is supplied by the canonical monoidal structure on
`localizedRestrictionDerived X U`; no chapter-specific representation of derived objects is
exposed on the public surface.
-/
@[stacks 08DL "localized restriction and derived internal Hom"]
noncomputable def comparison (K L : ModuleDerived.{z} X) :
    (localizedRestrictionDerived.{z} X U).obj ((ihom K).obj L) ⟶
      (ihom ((localizedRestrictionDerived.{z} X U).obj K)).obj
        ((localizedRestrictionDerived.{z} X U).obj L) :=
  CategoryTheory.Functor.OplaxMonoidal.InternalHom.comparison
    (localizedRestrictionDerived.{z} X U) K L

/-- Lemma 20.42.3 (08DL): localized restriction preserves the derived internal Hom, so the
canonical comparison is an isomorphism for every pair of derived objects. -/
@[stacks 08DL "localized restriction preserves derived internal Hom"]
instance comparison_isIso {K L : ModuleDerived.{z} X} :
    IsIso (comparison X U K L) := sorry

variable (K L : ModuleDerived.{z} X)

#synth IsIso (comparison X U K L)

end RingedSite.Hom.LocalizedRestriction.InternalHom
