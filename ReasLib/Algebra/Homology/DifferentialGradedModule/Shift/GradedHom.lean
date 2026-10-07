module

public import ReasLib.Algebra.Homology.DifferentialGradedModule.DifferentialGraded

/-!
# Homogeneous Maps and Source Shifts

This leaf complements the target-shift equivalence for closed homogeneous maps with the
source-shifted form.  It also provides the two canonical homogeneous identity maps relating a
differential graded module and one of its shifts.
-/

@[expose] public section

noncomputable section

universe u v

open CategoryTheory
open scoped DifferentialGradedModule

namespace DifferentialGradedModule.Shift

variable {R : Type u} [CommRing R]
variable {A : CochainDGAlgebra R}

/-- Reindexing a degree `-k` map after shifting its source by `k` gives degree zero. -/
theorem sourceTargetIndex (n k : ℤ) :
    (n + k) + (-k) = n := sorry

/-- Reindexing the source of a degree `-k` map recovers its original degree. -/
theorem sourceInputIndex (n k : ℤ) :
    (n - k) + k = n := sorry

/-- The target degree `n - k` is the homogeneous target degree `n + (-k)`. -/
theorem sourceOutputIndex (n k : ℤ) :
    n - k = n + (-k) := sorry

/-- Closed degree-`-k` homogeneous maps `M ⟶ N` are canonically DG-module maps
`M[k] ⟶ N`. -/
def sourceHomEquiv (M N : DifferentialGradedModule.{u, v} A) (k : ℤ) :
    ClosedGradedHom A M N (-k) ≃ (M[k] ⟶ N) where
  toFun f :=
    { hom := fun n ↦ ModuleCat.castLinearMap (congrArg N.X (sourceTargetIndex n k)) (f.1 (n + k))
      comm_d := sorry
      comm_smul := sorry }
  invFun g :=
    ⟨⟨fun n ↦ ModuleCat.castLinearMap (congrArg N.X (sourceOutputIndex n k))
          ((g.hom (n - k)).comp
            (ModuleCat.castLinearMap (congrArg M.X (sourceInputIndex n k).symm) LinearMap.id)),
        sorry⟩,
      sorry⟩
  left_inv := sorry
  right_inv := sorry

/-- The source-shift equivalence evaluates a homogeneous map in degree `n + k` and reindexes
its target to degree `n`. -/
theorem sourceHomEquiv_hom (M N : DifferentialGradedModule.{u, v} A) (k : ℤ)
    (f : ClosedGradedHom A M N (-k)) (n : ℤ) :
    (sourceHomEquiv M N k f).hom n =
      ModuleCat.castLinearMap (congrArg N.X (sourceTargetIndex n k)) (f.1 (n + k)) := sorry

/-- The target of the homogeneous identity `M ⟶ M[k]` is canonically the source degree. -/
theorem toGradedHomIndex (n k : ℤ) :
    n = (n + (-k)) + k := sorry

/-- The identity of `M`, regarded as a closed degree-`-k` homogeneous map `M ⟶ M[k]`. -/
def toGradedHom (M : DifferentialGradedModule.{u, v} A) (k : ℤ) :
    ClosedGradedHom A M (M[k]) (-k) :=
  ⟨⟨fun n ↦ ModuleCat.castLinearMap (congrArg M.X (toGradedHomIndex n k)) LinearMap.id,
      sorry⟩,
    sorry⟩

/-- The homogeneous identity `M ⟶ M[k]` is degreewise identity followed by reindexing. -/
theorem toGradedHom_apply (M : DifferentialGradedModule.{u, v} A) (k n : ℤ)
    (x : M.X n) :
    (toGradedHom M k).1 n x =
      cast (congrArg (fun i : ℤ ↦ (M.X i : Type v)) (toGradedHomIndex n k)) x := sorry

/-- The identity of `M`, regarded as a closed degree-`k` homogeneous map `M[k] ⟶ M`. -/
def fromGradedHom (M : DifferentialGradedModule.{u, v} A) (k : ℤ) :
    ClosedGradedHom A (M[k]) M k :=
  ⟨⟨fun _ ↦ LinearMap.id, sorry⟩, sorry⟩

/-- The homogeneous identity `M[k] ⟶ M` acts as the identity in every degree. -/
theorem fromGradedHom_apply (M : DifferentialGradedModule.{u, v} A) (k n : ℤ)
    (x : (M[k]).X n) :
    (fromGradedHom M k).1 n x = x := sorry

end DifferentialGradedModule.Shift
