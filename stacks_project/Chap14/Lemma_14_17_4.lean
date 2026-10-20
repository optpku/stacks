/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicTopology.SimplicialObject.InternalHom.Finiteness
import StacksCheckRecall

/-!
@stack 017L
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped Simplicial

noncomputable section

universe w v u

namespace CategoryTheory.SimplicialObject.internalHom

variable {C : Type u} [Category.{v} C] [HasBinaryCoproducts C] [HasFiniteLimits C]
variable (U : SSet.{w}) [U.ObjFinite] [U.Nonempty]
variable (T : SimplicialObject C)
variable [U.EventuallyDegenerate]

/- Lemma 14.17.4 (017L) (1): the finite-limit criterion constructs the simplicial internal
mapping object for a degreewise finite nonempty and eventually degenerate simplicial set. -/
@[stacks 017L]
#check (presheaf.isRepresentable.ofEventuallyDegenerate U T :
  Functor.IsRepresentable (presheaf U T))

section Degreewise

variable {M : SimplicialObject C}
variable (R : (presheaf U T).RepresentableBy M) (n : ℕ)

/- Lemma 14.17.4 (017L) (2): every chosen representation has, in degree `n`, the expected
universal property for the source `U ⊗ Δ[n]`. -/
@[stacks 017L]
#check (degree.representableBy n R :
  (degree.presheaf U T n).RepresentableBy
    (M.obj (Opposite.op (SimplexCategory.mk n))))

end Degreewise

end CategoryTheory.SimplicialObject.internalHom
