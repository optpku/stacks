module

public import Mathlib.LinearAlgebra.Quotient.Basic
public import ReasLib.Algebra.DirectSum.Decomposition.Transport
public import ReasLib.Algebra.Module.Graded.Action
public import ReasLib.Algebra.Module.Graded.Quotient
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Homogeneous quotients after restricting scalars

This leaf handles the common situation in which a quotient submodule is defined over a larger
scalar ring, while the grading and the downstream decomposition are recorded over a smaller
scalar ring.  The quotient carriers are canonically equivalent; the component family on the
larger-scalar quotient is the image of the smaller-scalar homogeneous pieces under that
equivalence.
-/

@[expose] public section

open scoped DirectSum

universe u v w w' uA

namespace DirectSum.Decomposition

variable {ι : Type u} [DecidableEq ι]
variable {R : Type v} [Ring R]
variable {S : Type w} [Ring S] [SMul R S]
variable {M : Type w'} [AddCommGroup M] [Module R M] [Module S M]
variable [IsScalarTower R S M]

/-- The componentwise `R`-grading on the quotient by an `S`-submodule.

The quotient map is viewed as `R`-linear, while the submodule remains owned by the larger scalar
ring `S`.  The same-scalar case is `quotientGrading` in the base quotient leaf. -/
@[reducible, stacks 052N "restricted-scalar quotient grading family"]
def quotientGradingRestrictScalars
    (𝒜 : ι → Submodule R M) (P : Submodule S M) :
    ι → Submodule R (M ⧸ P) :=
  fun i ↦ (𝒜 i).map (P.mkQ.restrictScalars R)

/-- The restricted-scalar quotient family is the transported image family from the canonical
`R`-quotient by `P.restrictScalars R`. -/
@[stacks 052N "restricted-scalar quotient grading transport"]
theorem quotientGradingRestrictScalars_eq_transport
    (𝒜 : ι → Submodule R M) (P : Submodule S M) :
    (fun i ↦
      ((𝒜 i).map (P.restrictScalars R).mkQ).map
        (Submodule.Quotient.restrictScalarsEquiv R P).toLinearMap) =
      quotientGradingRestrictScalars 𝒜 P := sorry

/-- The homogeneous quotient decomposition when the quotient submodule is specified over a larger
scalar ring `S` and the grading is over `R`.

The `hfamily` proof only identifies two presentations of the same image submodule.  All quotient
and decomposition data are explicit, so downstream users can consume this owner without rebuilding
the carrier equivalence or introducing a local scalar instance.
-/
@[reducible, stacks 052N "homogeneous quotient decomposition under restricted scalars"]
noncomputable def quotientRestrictScalars
    (𝒜 : ι → Submodule R M) [DirectSum.Decomposition 𝒜]
    (P : Submodule S M)
    (hP : SetLike.IsHomogeneous 𝒜 (P.restrictScalars R)) :
    DirectSum.Decomposition (quotientGradingRestrictScalars 𝒜 P) := by
  let e : (M ⧸ P.restrictScalars R) ≃ₗ[R] (M ⧸ P) :=
    Submodule.Quotient.restrictScalarsEquiv R P
  -- Local instance justification (proof-local temporary data): the quotient decomposition is
  -- determined by the supplied homogeneity proof and is used only to transport this result.
  letI : DirectSum.Decomposition
      (fun i ↦ (𝒜 i).map (P.restrictScalars R).mkQ) :=
    DirectSum.Decomposition.quotientDecomposition 𝒜 hP
  let transported : DirectSum.Decomposition
      (fun i ↦ ((𝒜 i).map (P.restrictScalars R).mkQ).map e.toLinearMap) :=
    DirectSum.Decomposition.map
      (fun i ↦ (𝒜 i).map (P.restrictScalars R).mkQ) e
  have transported' : DirectSum.Decomposition
      (fun i ↦ ((𝒜 i).map (P.restrictScalars R).mkQ).map
        (Submodule.Quotient.restrictScalarsEquiv R P).toLinearMap) := by
    simpa [e] using transported
  rw [quotientGradingRestrictScalars_eq_transport (𝒜 := 𝒜) (P := P)] at transported'
  exact transported'

namespace quotientRestrictScalars

/-- The degree-`i` coordinate map for the canonical restricted-scalar quotient decomposition.

The decomposition selected by `hP` is kept inside this construction. Consumers can therefore use
this linear map without installing a proof-dependent `DirectSum.Decomposition` instance. -/
@[stacks 052N "restricted-scalar quotient component map"]
noncomputable def component
    (𝒜 : ι → Submodule R M) [DirectSum.Decomposition 𝒜]
    (P : Submodule S M)
    (hP : SetLike.IsHomogeneous 𝒜 (P.restrictScalars R))
    (i : ι) :
    M ⧸ P →ₗ[R] quotientGradingRestrictScalars 𝒜 P i := by
  letI : DirectSum.Decomposition (quotientGradingRestrictScalars 𝒜 P) :=
    quotientRestrictScalars 𝒜 P hP
  exact
    (DirectSum.component R ι (fun j ↦ quotientGradingRestrictScalars 𝒜 P j) i).comp
      (DirectSum.decomposeLinearEquiv (quotientGradingRestrictScalars 𝒜 P)).toLinearMap

/-- The canonical quotient coordinate of a homogeneous element is its quotient class. -/
@[stacks 052N "restricted-scalar quotient component formula"]
theorem component_mk
    (𝒜 : ι → Submodule R M) [DirectSum.Decomposition 𝒜]
    (P : Submodule S M)
    (hP : SetLike.IsHomogeneous 𝒜 (P.restrictScalars R))
    {i : ι} {x : M} (hx : x ∈ 𝒜 i) :
    ((component 𝒜 P hP i (P.mkQ x) : quotientGradingRestrictScalars 𝒜 P i) : M ⧸ P) =
      P.mkQ x := sorry

end quotientRestrictScalars

/-- The quotient class of a homogeneous element lands in the corresponding component of the
larger-scalar quotient presentation. -/
@[stacks 052N "restricted-scalar quotient component membership"]
theorem quotientRestrictScalars_mk_mem
    (𝒜 : ι → Submodule R M)
    (P : Submodule S M) {i : ι} {x : M} (hx : x ∈ 𝒜 i) :
    P.mkQ x ∈ quotientGradingRestrictScalars 𝒜 P i := sorry

/-- Compatibility coordinate statement for callers using `DirectSum.decompose` directly.

The pointwise API `quotientRestrictScalars.component_mk` avoids exposing the proof-dependent
decomposition instance in its public type. -/
@[stacks 052N "restricted-scalar quotient decomposition component"]
theorem quotientRestrictScalars_decompose_mk
    (𝒜 : ι → Submodule R M) [DirectSum.Decomposition 𝒜]
    (P : Submodule S M)
    (hP : SetLike.IsHomogeneous 𝒜 (P.restrictScalars R))
    {i : ι} {x : M} (hx : x ∈ 𝒜 i) :
    -- Local instance justification (proof-local temporary data): `decompose` needs the
    -- decomposition constructed from this theorem's explicit homogeneity witness.
    letI := quotientRestrictScalars 𝒜 P hP
    ((DirectSum.decompose
        (quotientGradingRestrictScalars 𝒜 P) (P.mkQ x) i :
        quotientGradingRestrictScalars 𝒜 P i) : M ⧸ P) = P.mkQ x := sorry

namespace quotientGradingRestrictScalars

variable {ιA : Type uA} [VAdd ιA ι]
variable [Module R S]

/-- Stacks `052N`: homogeneous scalar multiplication descends to a quotient presented with a
larger scalar ring, while the grading remains over the base ring. -/
@[stacks 052N "restricted-scalar quotient graded action membership"]
theorem smul_mem
    (𝒜 : ιA → Submodule R S) (ℳ : ι → Submodule R M) (P : Submodule S M)
    [SetLike.GradedSMul 𝒜 ℳ]
    {i : ιA} {j : ι} {a : S} {x : M ⧸ P}
    (ha : a ∈ 𝒜 i)
    (hx : x ∈ quotientGradingRestrictScalars ℳ P j) :
    a • x ∈ quotientGradingRestrictScalars ℳ P (i +ᵥ j) := sorry

/-- Stacks `052N`: package the canonical graded action on the restricted-scalar quotient family.

The quotient map is the standard `Submodule.mkQ`; the owner is independent of any particular
polynomial or chapter presentation. -/
@[reducible, stacks 052N "restricted-scalar quotient graded action"]
def gradedSMul
    (𝒜 : ιA → Submodule R S) (ℳ : ι → Submodule R M) (P : Submodule S M)
    [SetLike.GradedSMul 𝒜 ℳ] :
    SetLike.GradedSMul 𝒜 (quotientGradingRestrictScalars ℳ P) where
  smul_mem := fun i j a x ha hx ↦ smul_mem 𝒜 ℳ P ha hx

end quotientGradingRestrictScalars

end DirectSum.Decomposition
