/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.Hypercovering.Properties
import StacksCheckRecall

namespace CategoryTheory

/- Lemma 25.12.2 (0DAV): a site with pullbacks and enough `B`-valued covering families admits a
fixed-target hypercovering lying degreewise in `B`, provided these covers remain covering after
adjoining one arrow from an object of `B`. -/
@[stacks 0DAV]
#check @Hypercovering.exists_degreewiseObjectsIn

/- The reusable owner exposes both family-level and component-level membership. -/
#check @Hypercovering.degreewiseObjectsIn.family
#check @Hypercovering.degreewiseObjectsIn.mem

/- The basis owner exposes the single-arrow closure step used by the construction. -/
#check @Limits.FormalCoproduct.IsBasisCovering.addSingleton

end CategoryTheory
