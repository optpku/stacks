module

public import ReasLib.NumberTheory.Padics.SqrtT
import StacksCheckRecall

/-!
# Example [Stacks 0HA0]

Without residue-field separability, the mod-square description of wild inertia
in Lemma 09EE (6) can fail. The mixed-characteristic quadratic
`A = ℤ_[2][t]_{(2)}`, `B = A[x] / (x ^ 2 - t)` is a counterexample.
-/

@[expose] public section

/- Example [Stacks 0HA0] (1) The equality in Lemma 09EE (6) is false without
the hypothesis that `κ(m)` is separable over the residue field of `A`: on the
quadratic `B = A[x] / (x ^ 2 - t)` over `A = ℤ_[2][t]_{(2)}`, mod-square inertia
is a proper subgroup of wild inertia. -/
@[stacks 0HA0] #check
  (PadicInt.SqrtT.modSquareInertia_ne_wildInertia :
    PadicInt.SqrtT.branch.modSquareInertia Gal(PadicInt.SqrtT.rootExtension/PadicInt.SqrtT.baseField) ≠
      PadicInt.SqrtT.branch.wildInertia Gal(PadicInt.SqrtT.rootExtension/PadicInt.SqrtT.baseField))

/- Example [Stacks 0HA0] (2) In the extension `B = A[x] / (x ^ 2 - t)`, one has
`σ(x) = -x = x - 2 * x` and the element `2 * x` does not lie in `m ^ 2`. -/
@[stacks 0HA0] #check (PadicInt.SqrtT.two_mul_root_notMem_sq :
  (2 : PadicInt.SqrtT.rootRing) * PadicInt.SqrtT.root ∉
    (Ideal.span {(2 : PadicInt.SqrtT.rootRing)}) ^ 2)

#check (PadicInt.SqrtT.root_sq :
  PadicInt.SqrtT.root ^ 2 =
    algebraMap PadicInt.SqrtT.base PadicInt.SqrtT.rootRing PadicInt.SqrtT.indet)

#check (PadicInt.SqrtT.gal_gen : PadicInt.SqrtT.gal PadicInt.SqrtT.gen = -PadicInt.SqrtT.gen)

#check (PadicInt.SqrtT.gal_gen_eq_sub :
  PadicInt.SqrtT.gal PadicInt.SqrtT.gen = PadicInt.SqrtT.gen - 2 * PadicInt.SqrtT.gen)

#check (PadicInt.SqrtT.rootRingToIntegralClosure_root :
  PadicInt.SqrtT.rootRingToIntegralClosure PadicInt.SqrtT.root = PadicInt.SqrtT.genIntegral)

#check (PadicInt.SqrtT.rootRingToIntegralClosure_bijective :
  Function.Bijective PadicInt.SqrtT.rootRingToIntegralClosure)

#check (PadicInt.SqrtT.branch_eq_span_two :
  PadicInt.SqrtT.branch =
    Ideal.span {(2 : integralClosure PadicInt.SqrtT.base PadicInt.SqrtT.rootExtension)})

#check (PadicInt.SqrtT.not_isSeparable_residue :
  ¬ Algebra.IsSeparable (IsLocalRing.maximalIdeal PadicInt.SqrtT.base).ResidueField
    PadicInt.SqrtT.branch.ResidueField)

#check (PadicInt.SqrtT.gal_smul_genIntegral :
  PadicInt.SqrtT.gal • PadicInt.SqrtT.genIntegral = -PadicInt.SqrtT.genIntegral)

#check (PadicInt.SqrtT.two_mul_genIntegral_notMem_sq :
  (2 : integralClosure PadicInt.SqrtT.base PadicInt.SqrtT.rootExtension) *
    PadicInt.SqrtT.genIntegral ∉ PadicInt.SqrtT.branch ^ 2)

#check (PadicInt.SqrtT.gal_mem_wildInertia :
  PadicInt.SqrtT.gal ∈
    PadicInt.SqrtT.branch.wildInertia Gal(PadicInt.SqrtT.rootExtension/PadicInt.SqrtT.baseField))

#check (PadicInt.SqrtT.gal_notMem_modSquareInertia :
  PadicInt.SqrtT.gal ∉
    PadicInt.SqrtT.branch.modSquareInertia Gal(PadicInt.SqrtT.rootExtension/PadicInt.SqrtT.baseField))
