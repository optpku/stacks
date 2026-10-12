/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.DirectSum.Decomposition
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.Algebra.Module.Graded.Action

/-!
# Quotients of internally graded modules

This leaf gives the additive and linear-algebraic core of quotienting an
internally graded module by a homogeneous submodule.  It deliberately depends
only on `DirectSum.Decomposition`: multiplication, a graded algebra, and an
ideal quotient belong in more specialized leaves.
-/

@[expose] public section

open scoped DirectSum

universe u v w

namespace DirectSum.Decomposition

variable {ι : Type u} [DecidableEq ι]
variable {R : Type v} [Ring R]
variable {M : Type w} [AddCommGroup M] [Module R M]

/-
API design: the quotient pieces stay expressed by the canonical Mathlib construction
`(ℳ i).map N.mkQ`.  The family owner below gives that carrier a stable name; the concrete descended
map and its two inverse laws remain separate fine-grained APIs, and `quotientDecomposition`
packages them as reducible class data without registering a global instance depending on a chosen
homogeneity proof.  The descended map is constructed through `Submodule.liftQ`, so its universal
property remains visible to both the statement and its downstream rewrite API.
-/

/-- The componentwise grading on the quotient by a homogeneous submodule.

The quotient is formed over the same scalar ring as the source grading.  A larger-scalar version is
provided by `quotientGradingRestrictScalars` in the restricted-scalars leaf. -/
@[reducible, stacks 052N "quotient grading family"]
def quotientGrading
    (ℳ : ι → Submodule R M) (N : Submodule R M) :
    ι → Submodule R (M ⧸ N) :=
  fun i ↦ (ℳ i).map N.mkQ

/-- The quotient map restricted to one homogeneous component of a module. -/
@[stacks 052N "homogeneous submodule quotient component map"]
def quotientComponentMap
    (ℳ : ι → Submodule R M) (N : Submodule R M) (i : ι) :
    ℳ i →ₗ[R] quotientGrading ℳ N i :=
  LinearMap.codRestrict
    (quotientGrading ℳ N i)
    (N.mkQ.domRestrict (ℳ i))
    (fun x ↦ ⟨x, x.2, rfl⟩)

/-- Decompose a source element and map every component to its corresponding
quotient component. -/
@[stacks 052N "homogeneous submodule quotient predecomposition"]
noncomputable def quotientPredecompose
    (ℳ : ι → Submodule R M) [DirectSum.Decomposition ℳ]
    (N : Submodule R M) :
    M →ₗ[R] DirectSum ι (fun i ↦ quotientGrading ℳ N i) :=
  (DirectSum.lmap fun i ↦ quotientComponentMap ℳ N i).comp
    (DirectSum.decomposeLinearEquiv ℳ).toLinearMap

/-- A homogeneous source element is sent to the corresponding quotient
component by `quotientPredecompose`. -/
@[stacks 052N "homogeneous quotient predecomposition on a component"]
theorem quotientPredecompose_eq_lof_of_mem
    (ℳ : ι → Submodule R M) [DirectSum.Decomposition ℳ]
    (N : Submodule R M) {x : M} {i : ι} (hx : x ∈ ℳ i) :
    quotientPredecompose ℳ N x =
      DirectSum.lof R ι (fun i ↦ quotientGrading ℳ N i) i
        (quotientComponentMap ℳ N i ⟨x, hx⟩) := sorry

/-- The quotient predecomposition vanishes on a homogeneous submodule. -/
@[stacks 052N "homogeneous quotient predecomposition vanishes"]
theorem quotientPredecompose_eq_zero_of_mem
    (ℳ : ι → Submodule R M) [DirectSum.Decomposition ℳ]
    {N : Submodule R M} (hN : SetLike.IsHomogeneous ℳ N) {x : M} (hx : x ∈ N) :
    quotientPredecompose ℳ N x = 0 := sorry

/-- A homogeneous submodule lies in the kernel of the quotient
predecomposition. -/
@[stacks 052N "homogeneous submodule in quotient predecomposition kernel"]
theorem ker_quotientPredecompose
    (ℳ : ι → Submodule R M) [DirectSum.Decomposition ℳ]
    {N : Submodule R M} (hN : SetLike.IsHomogeneous ℳ N) :
    N ≤ LinearMap.ker (quotientPredecompose ℳ N) := sorry

/-- The quotient predecomposition descended through a homogeneous submodule. -/
@[stacks 052N "homogeneous submodule quotient decomposition map"]
noncomputable def quotientDecompose
    (ℳ : ι → Submodule R M) [DirectSum.Decomposition ℳ]
    {N : Submodule R M} (hN : SetLike.IsHomogeneous ℳ N) :
    M ⧸ N →ₗ[R] DirectSum ι (fun i ↦ quotientGrading ℳ N i) :=
  let f : M →ₗ[R] DirectSum ι (fun i ↦ quotientGrading ℳ N i) :=
    quotientPredecompose ℳ N
  let hf : N ≤ LinearMap.ker f := ker_quotientPredecompose ℳ hN
  @Submodule.liftQ R M _ _ _ N R
    (DirectSum ι (fun i ↦ quotientGrading ℳ N i)) _ _ _ (RingHom.id R) f hf

namespace quotientDecompose

/-- Stacks `052N`: the degree-`i` coordinate map of the quotient by a homogeneous submodule.

Unlike `DirectSum.decompose`, this map carries the homogeneity witness explicitly and therefore
does not require consumers to install a proof-dependent decomposition instance. -/
@[stacks 052N "homogeneous quotient component map"]
noncomputable def component
    (ℳ : ι → Submodule R M) [DirectSum.Decomposition ℳ]
    {N : Submodule R M} (hN : SetLike.IsHomogeneous ℳ N) (i : ι) :
    M ⧸ N →ₗ[R] quotientGrading ℳ N i :=
  (DirectSum.component R ι (fun j ↦ quotientGrading ℳ N j) i).comp
    (quotientDecompose ℳ hN)

/-- Stacks `052N`: the quotient coordinate of a homogeneous representative is its quotient
class. -/
@[stacks 052N "homogeneous quotient component formula"]
theorem component_mk
    (ℳ : ι → Submodule R M) [DirectSum.Decomposition ℳ]
    {N : Submodule R M} (hN : SetLike.IsHomogeneous ℳ N)
    {i : ι} {x : M} (hx : x ∈ ℳ i) :
    ((component ℳ hN i (N.mkQ x) : quotientGrading ℳ N i) : M ⧸ N) = N.mkQ x := sorry

end quotientDecompose

/-- Recomposing `quotientDecompose` recovers the quotient class. -/
@[stacks 052N "homogeneous quotient decomposition recomposition"]
theorem recompose_comp_quotientDecompose
    (ℳ : ι → Submodule R M) [DirectSum.Decomposition ℳ]
    {N : Submodule R M} (hN : SetLike.IsHomogeneous ℳ N) :
    DirectSum.coeLinearMap (quotientGrading ℳ N) ∘ₗ quotientDecompose ℳ hN =
      LinearMap.id := sorry

/-- The quotient decomposition is the identity on the direct sum of its
quotient components. -/
@[stacks 052N "homogeneous quotient decomposition on components"]
theorem quotientDecompose_comp_recompose
    (ℳ : ι → Submodule R M) [DirectSum.Decomposition ℳ]
    {N : Submodule R M} (hN : SetLike.IsHomogeneous ℳ N) :
    quotientDecompose ℳ hN ∘ₗ DirectSum.coeLinearMap (quotientGrading ℳ N) =
      LinearMap.id := sorry

/-- The internal direct-sum decomposition on the quotient by a homogeneous
submodule, with degree-`i` piece the image of the source degree-`i` piece. -/
@[reducible, stacks 052N "homogeneous submodule quotient decomposition"]
noncomputable def quotientDecomposition
    (ℳ : ι → Submodule R M) [DirectSum.Decomposition ℳ]
    {N : Submodule R M} (hN : SetLike.IsHomogeneous ℳ N) :
    DirectSum.Decomposition (quotientGrading ℳ N) :=
  DirectSum.Decomposition.ofLinearMap
    (quotientGrading ℳ N)
    (quotientDecompose ℳ hN)
    (recompose_comp_quotientDecompose ℳ hN)
    (quotientDecompose_comp_recompose ℳ hN)

end DirectSum.Decomposition
