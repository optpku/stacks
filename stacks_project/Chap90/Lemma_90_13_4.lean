/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import stacks_project.Chap90.Definition_90_10_1_Schlessinger
public import stacks_project.Chap90.Definition_90_16_8_Predeformation
public import stacks_project.Chap90.Definition_90_27_1_MinimalVersal
public import stacks_project.Chap90.Remarks_90_5_2_IsoClass

/-!
# Existence of versal formal objects

A predeformation category over `C_Λ` that satisfies Schlessinger's conditions
(S1) and (S2) and has finite-dimensional tangent space admits a versal formal
object.
-/

@[expose] public section

open CategoryTheory ArtinianLocalAlgCat

universe u

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable {F : Type (u + 1)} [Category.{u + 1} F]
variable {p : F ⥤ ArtinianLocalAlgCat Λ k}

namespace CategoryTheory.Functor

/-- Predeformation categories are cofibered in groupoids. -/
instance instIsFiberedInGroupoids_op [IsPredeformationCategory p] :
    IsFibered.InGroupoids p.op :=
  IsPredeformationCategory.isCofiberedInGroupoids

/-- Lemma 90.13.4: if `p` is a predeformation category satisfying Schlessinger's
conditions (S1) and (S2), and if the tangent space
`(fiberIsoClassFunctor p).obj (dualNumber Λ k)` is finite-dimensional over `k`,
then `p` admits a versal formal object. -/
@[stacks 06IW]
theorem exists_isVersal (p : F ⥤ ArtinianLocalAlgCat Λ k)
    [IsPredeformationCategory p] [HasSchlessingerS1 p] [HasSchlessingerS2 p]
    [AddCommGroup ((fiberIsoClassFunctor p).obj (dualNumber Λ k))]
    [Module k ((fiberIsoClassFunctor p).obj (dualNumber Λ k))]
    [FiniteDimensional k ((fiberIsoClassFunctor p).obj (dualNumber Λ k))] :
    ∃ ξ : FormalObject p, FormalObject.IsVersal ξ := sorry

end CategoryTheory.Functor
