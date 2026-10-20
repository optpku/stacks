module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Pullback.Tensor
import StacksCheckRecall

@[expose] public section

/- Lemma 20.27.3: derived pullback commutes with the canonical fixed-right derived tensor, with
the comparison chosen compatibly with the two derived-functor counits. -/

open AlgebraicGeometry CategoryTheory
open scoped RingedSpaceDerivedPullback RingedTensor

universe u

namespace AlgebraicGeometry.RingedSpace

@[stacks 079U "derived pullback--tensor comparison"]
#check @ModuleDerived.Pullback.existsTensorIso

@[stacks 079U "derived pullback--tensor counit square"]
#check @ModuleDerived.Pullback.existsTensorIso_commSq

#check @ModuleDerived.Pullback.sourceCounit
#check @ModuleDerived.Pullback.targetCounit

end AlgebraicGeometry.RingedSpace

end
