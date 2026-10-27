/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalScheme.IdealComparison
public import ReasLib.AlgebraicGeometry.FormalScheme.ChosenFppf.Comparison

/-!
# Scheme-thickening colimits and ideals of definition
-/

@[expose] public section

universe u v

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open AlgebraicGeometry AlgebraicGeometry.ChosenBigFppfSite

namespace AlgebraicGeometry.FormalScheme

/-- On a quasi-compact EGA formal scheme, existence of a fundamental system of ideals
of definition is equivalent to a directed scheme-thickening colimit presentation of its
points sheaf, with all schemes bounded in the same chosen site. -/
theorem sheafOfPoints_isDirectedColimit_iff_exists_fundamentalSystem
    {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (hS : IsTerminal (𝒮.toScheme.obj S))
    (h𝒮 : Scheme.IsSmallBoundClosed
      (fun T : Scheme.{u} ↦ ∃ U : 𝒮.carrier, Nonempty (T ≅ 𝒮.toScheme.obj U)))
    (X : FormalScheme.{u}) [CompactSpace X.carrier]
    (hsize : ∃ T : 𝒮.carrier, X.size ≤ (𝒮.toScheme.obj T).size) :
    Nonempty (FundamentalSystem X) ↔
      ∃ (Λ : Type (max u v)) (_ : Preorder Λ) (_ : IsDirected Λ (· ≤ ·))
        (D : Λ ⥤ Sheaf (𝒮.bigTopology S) (Type (max u v))),
        IsDirectedAlgebraicSpaceThickeningColimit D
            ((sheafOfPoints 𝒮 S).obj X) ∧
          ∀ i : Λ, ∃ Z : Scheme.{u},
            (∃ T : 𝒮.carrier, Z.size ≤ (𝒮.toScheme.obj T).size) ∧
            Nonempty
              (D.obj i ≅
                (sheafOfPoints 𝒮 S).obj (Scheme.toFormalScheme.obj Z)) :=
  sorry

end AlgebraicGeometry.FormalScheme
