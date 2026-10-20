/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.DerivedCategory.ModulesOnCategory.QuasiCoherent.Chaotic
import StacksCheckRecall

@[expose] public section

/- Definition 21.43.1 (0GYV): `QC(𝒞, 𝒪)` is the full subcategory of derived modules for which
every canonical map `RΓ(V, K) ⊗ᴸ[𝒪(V)] 𝒪(U) ⟶ RΓ(U, K)` associated to `U ⟶ V` is an
isomorphism. -/
@[stacks 0GYV "canonical quasi-coherent derived modules"]
#check @CategoryTheory.ModulesOnCategory.Chaotic.isQuasiCoherent

@[stacks 0GYV "canonical quasi-coherent derived-module subcategory"]
#check @CategoryTheory.ModulesOnCategory.Chaotic.QC

/- The reusable owners expose the exact section functor, derived restriction, concrete
comparison map, and its membership API separately. -/
#check @CategoryTheory.ModulesOnCategory.chaoticSections
#check @CategoryTheory.ModulesOnCategory.chaoticSectionsExact
#check @CategoryTheory.ModulesOnCategory.chaoticRGamma
#check @CategoryTheory.ModulesOnCategory.chaoticDerivedRestrict
#check @CategoryTheory.ModulesOnCategory.chaoticComparison
#check @CategoryTheory.ModulesOnCategory.chaoticComparison_fac
#check @CategoryTheory.ModulesOnCategory.Chaotic.mem_iff
#check @CategoryTheory.ModulesOnCategory.Chaotic.comparison_isIso
