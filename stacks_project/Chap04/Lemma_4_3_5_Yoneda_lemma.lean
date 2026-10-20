/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.RepresentablePresheaf
import StacksCheckRecall

@[expose] public section


universe v u

namespace CategoryTheory

open scoped RepresentablePresheaf

variable {C : Type u} [Category.{v} C]
variable {U : C} {F : Cᵒᵖ ⥤ Type v}

/-
`Yoneda.fullyFaithful` and the unlifted `yonedaEquiv` are the canonical mathlib owners of the two
source clauses. The latter has values in the literal hom-set rather than the `ULift` used by the
universe-packaged `yonedaLemma`.
-/

/- Lemma 4.3.5 (Yoneda lemma) (1): for `U V : C`, every natural transformation
`s : h[U] ⟶ h[V]` is uniquely `yoneda.map φ` for a morphism `φ : U ⟶ V`; equivalently, the
Yoneda embedding is fully faithful. -/
@[stacks 001P "full faithfulness of the Yoneda embedding"]
#check (Yoneda.fullyFaithful (C := C) : (yoneda (C := C)).FullyFaithful)

/- Lemma 4.3.5 (Yoneda lemma) (2): for every presheaf `F` and object `U`, natural transformations
`h[U] ⟶ F` are naturally equivalent to elements of `F.obj (op U)`. -/
@[stacks 001P "natural evaluation bijection for representable presheaves"]
#check (yonedaEquiv (X := U) (F := F) :
  (yoneda.obj U ⟶ F) ≃ F.obj (Opposite.op U))

end CategoryTheory
