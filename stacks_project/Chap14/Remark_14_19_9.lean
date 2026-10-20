/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicTopology.SimplicialObject.Truncated.Coskeleton.Truncation
public import ReasLib.AlgebraicTopology.SimplexCategory.Truncated.KanExtension.FiniteInstances
import StacksCheckRecall

/-!
@stack 018A

# Source-facing recall for Remark 14.19.9

The inductive textbook construction is represented canonically by right Kan extension between
arbitrary truncation levels.  This avoids making a recursively chosen stage family a second public
owner for coskeleta.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.SimplicialObject

noncomputable section

universe u v

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [HasFiniteLimits C]
variable {n m : ℕ} (h : n ≤ m)

/- The canonical right Kan extension and its universal Hom-equivalence live in the truncation
owner namespace, rather than in the one-step successor facade. -/
#check SimplicialObject.Truncated.trunc.cosk.functor (C := C) n m h

#check SimplicialObject.Truncated.trunc.cosk.adj (C := C) n m h

#check SimplicialObject.Truncated.trunc.cosk.homEquiv (C := C) n m h
#check SimplicialObject.Truncated.trunc.cosk.homEquiv_apply (C := C) n m h
#check SimplicialObject.Truncated.trunc.cosk.homEquiv_symm_apply (C := C) n m h

/- Remark 14.19.9 (1): the direct right Kan extension is the canonical version of the recursively
constructed stage `U^m`. -/
@[stacks 018A "Remark 14.19.9 (1)"]
#check (SimplicialObject.Truncated.trunc.cosk.ranIso (C := C) n m h :
  SimplicialObject.Truncated.trunc.cosk.functor (C := C) n m h ≅
    (SimplicialObject.Truncated.cosk n :
      SimplicialObject.Truncated C n ⥤ SimplicialObject C) ⋙ truncation m)

variable (U : SimplicialObject.Truncated C n)

/- The functorial comparison reduces directly to the singular restriction isomorphism. -/
#check (SimplicialObject.Truncated.trunc.cosk.ranIso_app (C := C) n m h U)

/- Remark 14.19.9 (2): its universal mapping formula is the hom equivalence of the canonical
adjunction between the two truncation levels. -/
@[stacks 018A "Remark 14.19.9 (2)"]
#check (SimplicialObject.Truncated.trunc.cosk.adjunction (C := C) n m h :
  SimplicialObject.Truncated.trunc C m n h ⊣
    (SimplicialObject.Truncated.cosk n :
      SimplicialObject.Truncated C n ⥤ SimplicialObject C) ⋙ truncation m)
#check SimplicialObject.Truncated.cosk.ofLE.iso_hom
#check SimplicialObject.Truncated.cosk.ofLE.iso_inv
#check SimplicialObject.Truncated.Between.coskeleton.restriction.iso.inv_counit
#check SimplicialObject.Truncated.Between.skeleton.restriction.iso.unit_inv

/- Remark 14.19.9 (3): the endpoint mapping formula is the ambient coskeleton adjunction. -/
@[stacks 018A "Remark 14.19.9 (3)"]
#check (coskAdj (C := C) n :
  (truncation n : SimplicialObject C ⥤ SimplicialObject.Truncated C n) ⊣
    SimplicialObject.Truncated.cosk n)

end CategoryTheory
