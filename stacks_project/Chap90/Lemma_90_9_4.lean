module

public import Mathlib.Data.List.TFAE
public import ReasLib.RingTheory.Smooth.Adic.Basic
public import stacks_project.Chap90.Definition_90_6_2_Predeformation
public import stacks_project.Chap90.Definition_90_9_1_Smooth
public import stacks_project.Chap90.Definition_90_27_1_MinimalVersal
public import stacks_project.Chap90.Lemma_90_8_6_PowerSeries
public import stacks_project.Chap90.Lemma_90_9_3_Classical

/-!
# Unobstructed predeformation categories and versal bases

For a predeformation category with a versal formal object `ξ` over `R` in `Ĉ_Λ`,
unobstructedness is equivalent to `m_R`-adic formal smoothness of `Λ → R`. In the
classical case these are also equivalent to `R` being a finite-variable power
series ring over `Λ`.
-/

@[expose] public section

open CategoryTheory IsLocalRing ArtinianLocalAlgCat CompleteLocalAlgCat

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

/-- Lemma 90.9.4 (1): Let `p` be a predeformation category. Let `ξ` be a versal
formal object of `p` lying over `R = ξ.base` in `CompleteLocalAlgCat Λ k`. Then
`p` is unobstructed if and only if `algebraMap Λ ξ.base.carrier` is formally
smooth in the `maximalIdeal ξ.base.carrier`-adic topology. -/
@[stacks 0DZK]
theorem isUnobstructed_iff_formallySmooth [IsPredeformationCategory p]
    (ξ : FormalObject p) [FormalObject.IsVersal ξ] :
    IsUnobstructed p ↔
      (algebraMap Λ ξ.base.carrier).formally_smooth_for_adic
        (maximalIdeal ξ.base.carrier) :=
  sorry

/-- Lemma 90.9.4 (2): in the classical case, the equivalents of
`isUnobstructed_iff_formallySmooth` are also equivalent to
`IsPowerSeriesOver (fromClassical ξ.base)`. -/
@[stacks 0DZK]
theorem isUnobstructed_tfae_isClassical [IsPredeformationCategory p] [IsClassical Λ k]
    (ξ : FormalObject p) [FormalObject.IsVersal ξ] :
    List.TFAE
      [IsUnobstructed p,
        (algebraMap Λ ξ.base.carrier).formally_smooth_for_adic
          (maximalIdeal ξ.base.carrier),
        IsPowerSeriesOver (fromClassical ξ.base)] :=
  sorry

/-- In the classical case, unobstructedness of a predeformation category with a
versal formal object `ξ` is equivalent to `IsPowerSeriesOver (fromClassical ξ.base)`. -/
theorem isUnobstructed_iff_isPowerSeriesOver [IsPredeformationCategory p]
    [IsClassical Λ k] (ξ : FormalObject p) [FormalObject.IsVersal ξ] :
    IsUnobstructed p ↔ IsPowerSeriesOver (fromClassical ξ.base) :=
  sorry

end CategoryTheory.Functor
