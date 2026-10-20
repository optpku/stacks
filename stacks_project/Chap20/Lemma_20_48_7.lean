/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.TorDimension.Tensor
import StacksCheckRecall

@[expose] public section

/- Lemma 20.48.7: Tor-amplitude intervals add under the canonical derived tensor product. -/

open AlgebraicGeometry CategoryTheory
open scoped CategoryTheory.DerivedCategory.DerivedTensor

universe u

namespace AlgebraicGeometry.RingedSpace

/- The stalkwise proof route is an implementation bridge; the public statement is the intrinsic
  Tor-amplitude theorem below. -/
@[stacks 09J4 "Tor-amplitude tensor closure"]
#check @HasTorAmplitudeIn.tensor

end AlgebraicGeometry.RingedSpace

end
