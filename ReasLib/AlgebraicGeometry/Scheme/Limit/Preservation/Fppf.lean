/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.CategoryTheory.Sites.Sheaf
public import ReasLib.AlgebraicGeometry.Scheme.Cover.Fppf
public import ReasLib.AlgebraicGeometry.Scheme.Limit.Preservation

/-!
# Fppf locality of limit-preserving sheaves
-/

@[expose] public section

open CategoryTheory Opposite AlgebraicGeometry

universe u v w

namespace AlgebraicGeometry.Scheme.Over

/-- An fppf sheaf on schemes over `S` preserves directed affine limits if its
restriction along every arrow of an fppf cover of `S` does. -/
theorem preservesDirectedAffineLimits_of_fppfCover {S : Scheme.{u}}
    {F : (Over S)ᵒᵖ ⥤ Type v}
    (hF : Presheaf.IsSheaf (Scheme.fppfTopology.over S) F)
    (𝒰 : FppfCover.{u, w} S)
    (h𝒰 : ∀ j : 𝒰.I₀,
      PreservesDirectedAffineLimits (𝒰.X j) ((Over.map (𝒰.f j)).op ⋙ F)) :
    PreservesDirectedAffineLimits S F := sorry

/-- An fppf sheaf on schemes over `S` preserves directed affine limits if its
restriction along every arrow of an indexed fppf covering family does. -/
theorem preservesDirectedAffineLimits_of_fppfCovering {S : Scheme.{u}}
    {F : (Over S)ᵒᵖ ⥤ Type v}
    (hF : Presheaf.IsSheaf (Scheme.fppfTopology.over S) F)
    {J : Type w} (U : J → Over S) (hU : Scheme.FppfCovering U)
    (h : ∀ j : J,
      PreservesDirectedAffineLimits (U j).left ((Over.map (U j).hom).op ⋙ F)) :
    PreservesDirectedAffineLimits S F := sorry

end AlgebraicGeometry.Scheme.Over
