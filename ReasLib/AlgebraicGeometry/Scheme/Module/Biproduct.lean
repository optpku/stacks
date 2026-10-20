/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf

/-!
# Finite biproducts of scheme module sheaves

The canonical Abelian structure on `X.Modules` supplies finite biproducts of
module sheaves on a scheme.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

/-- The category of module sheaves on a scheme has finite biproducts. -/
noncomputable instance moduleHasFiniteBiproducts (X : Scheme.{u}) :
    HasFiniteBiproducts X.Modules :=
  CategoryTheory.Abelian.hasFiniteBiproducts

end AlgebraicGeometry.Scheme

end
