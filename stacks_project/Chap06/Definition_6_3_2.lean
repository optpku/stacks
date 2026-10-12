/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Topology.Sheaves.Presheaf
import StacksCheckRecall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory TopologicalSpace TopCat

universe u v

/-
The canonical data owner is `Functor.const`: specializing its indexing category to `(Opens X)ᵒᵖ`
gives exactly the source presheaf, with object values and restriction maps controlled by
`Functor.const_obj_obj` and `Functor.const_obj_map`. No project-local alias or notation is needed
for this standard functor-category construction.
-/

variable (X : TopCat.{u}) (A : Type v)

/- Definition 6.3.2: the constant presheaf construction on `X` is the specialization of the
canonical constant-functor owner to the opposite category of open subsets of `X`. -/
@[stacks 006F "constant presheaf functor on open subsets"]
#check (Functor.const (Opens X)ᵒᵖ : Type v ⥤ X.Presheaf (Type v))

/- Evaluating the owner at `A` gives the source presheaf; `Functor.const_obj_obj` and
`Functor.const_obj_map` state that every open receives `A` and every restriction is `𝟙 A`. -/
#check ((Functor.const (Opens X)ᵒᵖ).obj A : X.Presheaf (Type v))
#check Functor.const_obj_obj
#check Functor.const_obj_map
