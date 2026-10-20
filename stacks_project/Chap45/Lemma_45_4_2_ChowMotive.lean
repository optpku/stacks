/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.ChowMotive

@[expose] public section

open CategoryTheory

universe w v u

variable (k : Type u) [Field k]
variable (GradedCorrespondence : Type u → Type v)
variable [Category.{w} (GradedCorrespondence k)]

#check (ChowMotive.isIdempotentComplete k GradedCorrespondence :
  IsIdempotentComplete (ChowMotive k GradedCorrespondence))
