/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicTopology.SimplicialObject.Truncated.Coskeleton.Truncation
public import ReasLib.AlgebraicTopology.SimplexCategory.Truncated.KanExtension.FiniteInstances
import StacksCheckRecall

/-!
@stack 018B

# Lemma 14.19.10 compatibility facade

ReasLib owns the coskeleton adjunctions and comparison isomorphisms. Mathlib owns coskeletality
and its unit-isomorphism criterion; ReasLib adds isomorphism invariance and monotonicity in the
truncation level.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.SimplicialObject

noncomputable section

universe u v

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [HasFiniteLimits C]

section AmbientCoskeleton

variable (n : ℕ)

/- Lemma 14.19.10 (1): truncation at `n` has the canonical `n`-coskeleton as right adjoint. -/
@[stacks 018B "Lemma 14.19.10 (1)"]
#check (coskAdj n :
  (truncation n : SimplicialObject C ⥤ SimplicialObject.Truncated C n) ⊣
    SimplicialObject.Truncated.cosk n)

/- The counit is invertible because right Kan extension along the fully faithful truncated-simplex
inclusion is reflective. -/
#check (inferInstance : IsIso (coskAdj (C := C) n).counit)

end AmbientCoskeleton

section FurtherTruncation

variable {n m : ℕ} (h : n ≤ m)

/- Lemma 14.19.10 (2): further truncation from level `m` to level `n` has right adjoint obtained by
taking the ambient `n`-coskeleton and truncating it back to level `m`. -/
@[stacks 018B "Lemma 14.19.10 (2)"]
#check (SimplicialObject.Truncated.trunc.cosk.adjunction (C := C) n m h :
  SimplicialObject.Truncated.trunc C m n h ⊣
    (SimplicialObject.Truncated.cosk n :
      SimplicialObject.Truncated C n ⥤ SimplicialObject C) ⋙ truncation m)

variable (U : SimplicialObject.Truncated C n)

/- Lemma 14.19.10 (3): the `m`-coskeleton of the `m`-truncation of an `n`-coskeleton is
canonically isomorphic to that `n`-coskeleton. -/
@[stacks 018B "Lemma 14.19.10 (3)"]
#check ((SimplicialObject.Truncated.cosk.ofLE.compIso (C := C) n m h).app U :
  (SimplicialObject.Truncated.cosk m).obj
      ((truncation m).obj ((SimplicialObject.Truncated.cosk n).obj U)) ≅
    (SimplicialObject.Truncated.cosk n).obj U)
#check (SimplicialObject.Truncated.cosk.ofLE.compIso_app (C := C) n m h U)

/- The reusable objectwise owner needs only the two chosen coskeletons in this comparison. -/
#check (SimplicialObject.Truncated.coskeleton.ofLE.iso U h)

/- The functorial comparison exposes its objectwise component without unfolding `NatIso`. -/
#check (SimplicialObject.Truncated.cosk.ofLE.natIso_app (C := C) n m h U)

end FurtherTruncation

section Monotonicity

variable {n m : ℕ} (h : n ≤ m) (X : SimplicialObject C)
variable (hn : IsIso ((coskAdj n).unit.app X))

/- Lemma 14.19.10 (4): invertibility of the coskeleton unit is monotone in the truncation level. -/
@[stacks 018B "Lemma 14.19.10 (4)"]
#check (SimplicialObject.coskAdj.unit.isIso_of_le.explicit h hn :
  IsIso ((coskAdj m).unit.app X))

/- The canonical owner-level formulation is monotonicity of `SimplicialObject.IsCoskeletal`. -/
#check SimplicialObject.IsCoskeletal.ofLE

end Monotonicity

end CategoryTheory
