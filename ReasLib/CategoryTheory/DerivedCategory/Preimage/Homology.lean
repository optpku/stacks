/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import ReasLib.CategoryTheory.DerivedCategory.Truncation.Homology
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Homology of a chosen derived-category preimage

`DerivedCategory.Q.objPreimage` is a canonical representative selected by the localization.
This leaf exposes the homology comparison and the lower-bound transport needed by truncation and
injective-resolution constructions, without depending on a site or a chapter file.
-/

open CategoryTheory
open DerivedCategory

universe w v u

namespace CategoryTheory.DerivedCategory.Preimage

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜] [HasDerivedCategory.{w} 𝒜]

/-- The homology of a derived object is canonically the homology of its chosen cochain preimage. -/
@[stacks 0EZB "homology of a chosen derived preimage"]
noncomputable def homologyIso (K : DerivedCategory 𝒜) (i : ℤ) :
    (DerivedCategory.homologyFunctor 𝒜 i).obj K ≅
      (DerivedCategory.Q.objPreimage K).homology i :=
  ((DerivedCategory.homologyFunctor 𝒜 i).mapIso
      (DerivedCategory.Q.objObjPreimageIso K)).symm ≪≫
    (DerivedCategory.homologyFunctorFactors 𝒜 i).app
      (DerivedCategory.Q.objPreimage K)

/-- Lemma 21.30.4 (0EZB): a lower cohomological bound on a derived object descends to its
chosen cochain-complex preimage. -/
@[stacks 0EZB "lower bound of a chosen derived preimage"]
theorem isGE_of_isGE (K : DerivedCategory 𝒜) {m : ℤ}
    (hK : K.IsGE m) :
    (DerivedCategory.Q.objPreimage K).IsGE m := sorry

end CategoryTheory.DerivedCategory.Preimage

end
