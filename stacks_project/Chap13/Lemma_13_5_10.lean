/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.CategoryTheory.MorphismProperty.Localization.Triangulated.DenominatorTriangle
import StacksCheckRecall

@[expose] public section

namespace CategoryTheory

/- Lemma 13.5.10 (1): denominators under a distinguished triangle form a filtered category. -/
@[stacks 05R9 "filtered category of denominators under a distinguished triangle"]
#check @MorphismProperty.TriangleDenominator.isFiltered

/- Lemma 13.5.10 (2): the first vertex projection is final. -/
@[stacks 05R9 "first final projection from triangle denominators"]
#check @MorphismProperty.TriangleDenominator.projection₁_final

/- Lemma 13.5.10 (3): the second vertex projection is final. -/
@[stacks 05R9 "second final projection from triangle denominators"]
#check @MorphismProperty.TriangleDenominator.projection₂_final

/- Lemma 13.5.10 (4): the third vertex projection is final. -/
@[stacks 05R9 "third final projection from triangle denominators"]
#check @MorphismProperty.TriangleDenominator.projection₃_final

end CategoryTheory
