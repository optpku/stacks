/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.ChosenFppf.Basic
public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.ChosenFppf.Thickening

/-!
# Directed colimits of formal algebraic spaces

Nonempty directed colimits along relative thickenings preserve formal algebraic
spaces, and affine formal algebraic spaces in particular, when the colimit
satisfies the fixed-site presentation condition.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.GrothendieckTopology
open AlgebraicGeometry.ChosenBigFppfSite

noncomputable section

universe u v

namespace AlgebraicGeometry
namespace IsAffineFormalAlgebraicSpace

/-- A nonempty directed colimit of affine formal algebraic spaces along
relative thickenings is an affine formal algebraic space, provided the colimit
admits a coequalizer presentation by representables from the same fixed chosen
big fppf site. The fixed-site presentation is supplied by `h_size`. -/
theorem of_directedColimit {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    {Λ : Type (max u v)} [Preorder Λ] [IsDirected Λ (· ≤ ·)] [Nonempty Λ]
    (F : Λ ⥤ Sheaf (𝒮.bigTopology S) (Type (max u v)))
    (h_affine : ∀ i, IsAffineFormalAlgebraicSpace (F.obj i))
    (h_thickening : ∀ {i j : Λ} (f : i ⟶ j), isRelativeThickening (F.map f))
    (c : Cocone F) (hc : IsColimit c)
    (h_size : AlgebraicGeometry.ChosenBigFppfSite.IsCoequalizerOfRepresentables c.pt) :
    IsAffineFormalAlgebraicSpace c.pt :=
  sorry

end IsAffineFormalAlgebraicSpace

namespace IsFormalAlgebraicSpace

/-- A nonempty directed colimit of formal algebraic spaces along relative
thickenings is a formal algebraic space, provided the colimit admits a
coequalizer presentation by representables from the same fixed chosen big fppf
site. The fixed-site presentation is supplied by h_size. -/
theorem of_directedColimit {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    {Λ : Type (max u v)} [Preorder Λ] [IsDirected Λ (· ≤ ·)] [Nonempty Λ]
    (F : Λ ⥤ Sheaf (𝒮.bigTopology S) (Type (max u v)))
    (h_formal : ∀ i, IsFormalAlgebraicSpace (F.obj i))
    (h_thickening : ∀ {i j : Λ} (f : i ⟶ j),
      IsAffineFormalAlgebraicSpace.isRelativeThickening (F.map f))
    (c : Cocone F) (hc : IsColimit c)
    (h_size : AlgebraicGeometry.ChosenBigFppfSite.IsCoequalizerOfRepresentables c.pt) :
    IsFormalAlgebraicSpace c.pt :=
  sorry

end IsFormalAlgebraicSpace
end AlgebraicGeometry
