module

public import stacks_project.Chap90.«90_3_10_2_ConormalSequence»
public import stacks_project.Chap90.«90_3_10_2_ResidueAlgebra»
import StacksCheckRecall

/-!
# Extended naive-cotangent sequence

For a `Λ`-algebra `A` equipped with a `Λ`-algebra surjection `A → k` (in particular any object
of `C_Λ`), the naive-cotangent Jacobi–Zariski sequence of `Λ → A → k` extends the conormal
sequence to
`H1Cotangent Λ k → (ker (algebraMap A k)).Cotangent → k ⊗[A] Ω[A⁄Λ] → Ω[k⁄Λ] → 0`.
-/

@[expose] public section

open scoped TensorProduct
open Algebra.H1Cotangent KaehlerDifferential

/- 90.3.10.2 (1): the first arrow `H1Cotangent Λ k → (ker (algebraMap A k)).Cotangent`
of the extended naive-cotangent sequence. -/
@[stacks 06S7] #check @toConormal

/- 90.3.10.2 (2): the source map `d_A` is `kerCotangentToTensor`, landing in
`k ⊗[A] Ω[A⁄Λ]` (mathlib tensor order). -/
@[stacks 06S7] #check @kerCotangentToTensor

/- 90.3.10.2 (3): exactness at `m_A / m_A²`, i.e. at `(ker (algebraMap A k)).Cotangent`. -/
@[stacks 06S7] #check @exact_toConormal_kerCotangentToTensor

/- 90.3.10.2 (4): exactness at `Ω[A⁄Λ] ⊗[A] k`, i.e. at `k ⊗[A] Ω[A⁄Λ]`. -/
@[stacks 06S7] #check @exact_kerCotangentToTensor_mapBaseChange

/- 90.3.10.2 (5): the terminal map `k ⊗[A] Ω[A⁄Λ] → Ω[k⁄Λ]` is surjective. -/
@[stacks 06S7] #check @mapBaseChange_surjective
