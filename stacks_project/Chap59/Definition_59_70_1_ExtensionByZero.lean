/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.ExtensionByZero

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

noncomputable section

universe u w u₁ v₁

namespace AlgebraicGeometry.Scheme

variable {U X : Scheme.{u}}

#check (etaleRestrictionSheaf)
#check (etaleRestrictionSheaf_def)
#check (etaleRestrictionSheaf_isRightAdjoint)
#check (etaleExtensionByZero)
#check (etaleExtensionByZero_def)
#check (etaleExtensionByZero_adjunction)
#check (sheafExtensionByZero)
#check (sheafExtensionByZero_def)
#check (sheafExtensionByZero_adjunction)
#check (abelianExtensionByZero)
#check (abelianExtensionByZero_def)
#check (abelianExtensionByZero_adjunction)
#check (moduleExtensionByZero)
#check (moduleExtensionByZero_def)
#check (moduleExtensionByZero_adjunction)

end AlgebraicGeometry.Scheme
