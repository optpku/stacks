/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Pullback
public import ReasLib.CategoryTheory.Sites.Presheaf.InverseImage
import StacksCheckRecall

open CategoryTheory
open AlgebraicGeometry

universe u v

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/- Definition 59.35.1: the small étale direct image of a presheaf is
precomposition with the opposite of the canonical small étale pullback,
so its value at an étale object V over Y is the original presheaf evaluated
at the corresponding base-changed étale object over X. -/
@[stacks 03PW] #check
  (CategoryTheory.Functor.presheafInverseImage
    (AlgebraicGeometry.Scheme.smallEtalePullback f) (Type v) :
    (X.Etaleᵒᵖ ⥤ Type v) ⥤ (Y.Etaleᵒᵖ ⥤ Type v))
