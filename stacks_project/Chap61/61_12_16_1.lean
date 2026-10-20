/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Proetale.SmallToBig

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.Scheme

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.ProEt
namespace SmallToBig

/- 61.12.16.1: restricting the big pro-étale direct image of a sheaf to the
small pro-étale site agrees with the small pro-étale direct image of its
restriction. -/
@[stacks 0F60]
#check (AlgebraicGeometry.Scheme.ProEt.SmallToBig.bigToSmall_pushforward_eq :
  ∀ {S T : Scheme.{u}} (f : T ⟶ S)
    (F : Sheaf (proetaleTopology.{u}.over T) (Type (u + 1))),
    (restrictToSmall S).obj ((bigPushforward f).obj F) =
      (smallPushforward f).obj ((restrictToSmall T).obj F))

end SmallToBig
end AlgebraicGeometry.Scheme.ProEt

end
