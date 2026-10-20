/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Monoidal.Closed.Source
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open CategoryTheory.MonoidalClosed

namespace AlgebraicGeometry.RingedSpace

/- Lemma 20.42.9 (0A8U) is the ringed-space specialization of the generic source-order
tensor-to-iterated-internal-Hom map.  The reusable owner is kept independent of Chapter 20. -/
@[stacks 0A8U]
#check @CategoryTheory.MonoidalClosed.Source.Iterated.map

#check @CategoryTheory.MonoidalClosed.Source.Iterated.map_spec
#check @CategoryTheory.MonoidalClosed.Source.Iterated.map_uncurry
#check @CategoryTheory.MonoidalClosed.Source.comp_natural_target
#check @CategoryTheory.MonoidalClosed.Source.comp_natural_target_assoc
#check @CategoryTheory.MonoidalClosed.Source.comp_natural_source
#check @CategoryTheory.MonoidalClosed.Source.comp_natural_source_assoc
#check @CategoryTheory.MonoidalClosed.Source.comp_natural_middle
#check @CategoryTheory.MonoidalClosed.Source.tensor
#check @CategoryTheory.MonoidalClosed.Source.tensor_spec

end AlgebraicGeometry.RingedSpace
