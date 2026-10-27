/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.AlgebraicGeometry.Scheme.Model.Stable
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom

/- Lemma 109.24.2: Let `R` be a discrete valuation ring with fraction field `K`.
Let `C` be a smooth proper curve over `K` with `H⁰(C, 𝒪_C) = K` and genus `g`.
If `X` and `X'` are models of `C` and both are stable families of genus `g`
curves over `R`, then there is a unique isomorphism of models `X ⟶ X'`. -/
@[stacks 0E97] #check (AlgebraicGeometry.Scheme.Hom.Model.existsUnique_stableIso :
  ∀ (R K : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (C : SchemeOverField K) [Curve C] [Smooth C.hom] [IsProper C.hom]
    (h_globalSections : Function.Bijective (Scheme.Hom.globalSectionsMap C.hom))
    (g : ℕ)
    (h_genus :
      SchemeOverField.genus C (topologicalKrullDim_eq_one C) h_globalSections = g)
    (X X' : Model R K C) [IsProper X.base] [IsProper X'.base]
    [IsStableFamily X.base] [IsStableFamily X'.base]
    (hX : IsStableFamilyOfGenus g X.base)
    (hX' : IsStableFamilyOfGenus g X'.base),
    ∃! e : Over.mk X.base ≅ Over.mk X'.base, Model.IsMorphism X X' e.hom)

end AlgebraicGeometry.Scheme.Hom
