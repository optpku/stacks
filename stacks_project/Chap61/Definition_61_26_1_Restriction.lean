/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.ProEtale.Restriction

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.ProEt

variable {U X : Scheme.{u}} (j : U ⟶ X) [WeaklyEtale j]

#check (restriction j : U.ProEt ⥤ X.ProEt)
#check (restriction_isContinuous j :
  Functor.IsContinuous (restriction j) (topology U) (topology X))

end AlgebraicGeometry.Scheme.ProEt
