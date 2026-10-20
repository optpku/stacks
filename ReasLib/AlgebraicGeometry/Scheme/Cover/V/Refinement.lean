/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Cover.AffineFamily.Refinement
public import ReasLib.AlgebraicGeometry.Scheme.Cover.V.Basic

/-!
# Refinements and coproducts of valuative covers

The concrete operations on finite affine families are topology-independent and
are reexported from `Scheme.Cover.AffineFamily.Refinement`. This leaf adds
their closure and characterization properties for standard `V` covers.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

noncomputable section

namespace AffineFamilyOver

variable {T : Scheme.{u}}

namespace IsStandardVCover

/-- A composite of standard `V` covers is a standard `V` cover. -/
theorem comp {family : AffineFamilyOver T} [IsAffine T]
    (hfamily : IsStandardVCover family)
    (refining : (i : Fin family.n) → AffineFamilyOver (family.U i))
    (hrefining : ∀ i, IsStandardVCover (refining i)) :
    IsStandardVCover (family.comp refining) := sorry

end IsStandardVCover

/-- Over an affine target, a finite affine family is a standard `V` cover if
and only if it admits a refinement that is a standard `V` cover. -/
theorem isStandardVCover_iff_exists_refinement [IsAffine T]
    (family : AffineFamilyOver T) :
    IsStandardVCover family ↔
      ∃ (refining : AffineFamilyOver T)
        (refinement : Refinement refining family), IsStandardVCover refining := sorry

/-- Over an affine target, a finite affine family is a standard `V` cover if
and only if its coproduct map, regarded as a singleton affine family, is a
standard `V` cover. -/
theorem isStandardVCover_iff_coproductSingleton [IsAffine T]
    (family : AffineFamilyOver T) :
    IsStandardVCover family ↔ IsStandardVCover (coproductSingleton family) := sorry

variable {T' : Scheme.{u}}

namespace IsStandardVCover

/-- Standard `V` covers remain standard after affine base change. -/
theorem pullback {family : AffineFamilyOver T}
    (hfamily : IsStandardVCover family) (g : T' ⟶ T) [IsAffine T'] :
    IsStandardVCover (pullback family g) := sorry

end IsStandardVCover

end AffineFamilyOver

end

end AlgebraicGeometry
