/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Filtration.Strict.MonoEpi
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace CategoryTheory.FilteredObject.Hom

variable {C : Type u} [Category.{v} C] [HasImages C] [HasPullbacks C] [HasEqualizers C]
variable {A B : FilteredObject C} (f : A ⟶ B)

section Mono

variable [Mono f.hom]

/- Lemma 12.19.7 [0124] (1): a monomorphism is strict exactly when its source carries the induced
filtration. -/
@[stacks 0124]
#check (strict_iff_induced_filtration_of_mono f :
  Strict f ↔ A.filtration = (Subobject.pullback f.hom).toOrderHom.comp B.filtration)

end Mono

section Epi

variable [Balanced C] [Epi f.hom]

/- Lemma 12.19.7 [0124] (2): an epimorphism is strict exactly when its target carries the quotient
filtration. -/
@[stacks 0124]
#check (strict_iff_quotient_filtration_of_epi f :
  Strict f ↔ B.filtration = A.filtration.quotient f.hom)

end Epi

end CategoryTheory.FilteredObject.Hom
