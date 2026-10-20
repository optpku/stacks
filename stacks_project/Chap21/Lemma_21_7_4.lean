/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Pushforward.Presheaf
import StacksCheckRecall

/-!
Lemma 21.7.4 (072W) is recalled through the module-valued higher-direct-image comparison.
The primary owner keeps the `O_Y`-module structure and exposes both a functor-level `Iso` and
its coefficient component.  The underlying-additive sheaf is a view, not the root statement.
-/

open CategoryTheory

noncomputable section

namespace RingedSite.Hom.HigherDirectImage.Presheaf

/- Lemma 21.7.4 (072W): source-facing module-valued comparison. -/
@[stacks 072W "sheafified module cohomology presheaf equals higher direct image"]
#check @iso

@[stacks 072W "coefficient component of the module higher-direct-image comparison"]
#check @objIso

/- The underived comparison and its derived transport are reusable infrastructure. -/
@[stacks 072W "underived module pushforward comparison"]
#check @underivedIso

@[stacks 072W "naturality of the underived module pushforward comparison component"]
#check @underivedAppIso_naturality

@[stacks 072W "derived module pushforward comparison"]
#check @pushforwardDerivedIso

@[stacks 072W "coefficient naturality of the module higher-direct-image comparison"]
#check @objIso_hom_naturality

end RingedSite.Hom.HigherDirectImage.Presheaf

end
