/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Limit.Preservation.Fppf
import StacksCheckRecall

/-!
# Fppf locality of limit-preserving sheaves
-/

@[expose] public section

open CategoryTheory Opposite AlgebraicGeometry

universe u v w

namespace AlgebraicGeometry.Scheme.Over

/- Lemma 70.3.8: if `F : (Over S)ᵒᵖ ⥤ Type v` is a sheaf for
`Scheme.fppfTopology.over S` and `{U_j ⟶ S}` is an fppf covering such that each
restriction `(Over.map (U_j ⟶ S)).op ⋙ F` preserves directed affine limits,
then `F` preserves directed affine limits. -/
@[stacks 049P] #check
  (AlgebraicGeometry.Scheme.Over.preservesDirectedAffineLimits_of_fppfCover :
    ∀ {S : Scheme.{u}}
    {F : (Over S)ᵒᵖ ⥤ Type v}
    (hF : Presheaf.IsSheaf (Scheme.fppfTopology.over S) F)
    (𝒰 : FppfCover.{u, w} S)
    (h𝒰 : ∀ j : 𝒰.I₀,
      PreservesDirectedAffineLimits (𝒰.X j) ((Over.map (𝒰.f j)).op ⋙ F)),
      PreservesDirectedAffineLimits S F)

/- An fppf sheaf on `Over S` that is limit preserving after restriction along
an indexed fppf covering family `{U_j ⟶ S}` is limit preserving. -/
#check
  (AlgebraicGeometry.Scheme.Over.preservesDirectedAffineLimits_of_fppfCovering :
    ∀ {S : Scheme.{u}}
    {F : (Over S)ᵒᵖ ⥤ Type v}
    (hF : Presheaf.IsSheaf (Scheme.fppfTopology.over S) F)
    {J : Type w} (U : J → Over S) (hU : Scheme.FppfCovering U)
    (h : ∀ j : J,
      PreservesDirectedAffineLimits (U j).left ((Over.map (U j).hom).op ⋙ F)),
      PreservesDirectedAffineLimits S F)

end AlgebraicGeometry.Scheme.Over
