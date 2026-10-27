/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.Order.Directed
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ChosenFppf
public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.ChosenFppf.Basic
public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.ChosenFppf.Thickening

/-!
# Directed algebraic-space thickening colimits

A sheaf on `(Sch/S)_fppf` is a nonempty directed colimit of algebraic spaces along
thickening transitions when the stages are algebraic spaces, each transition
is a relative thickening, and the sheaf is isomorphic to a colimit cocone.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.GrothendieckTopology
open AlgebraicGeometry.ChosenBigFppfSite

noncomputable section

universe u v

namespace AlgebraicGeometry

/-- A nonempty directed diagram of algebraic-space sheaves with relative
thickening transitions has sheaf colimit isomorphic to `X`. -/
def IsDirectedAlgebraicSpaceThickeningColimit
    {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    {Λ : Type (max u v)} [Preorder Λ] [IsDirected Λ (· ≤ ·)]
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (D : Λ ⥤ Sheaf (𝒮.bigTopology S) (Type (max u v)))
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v))) : Prop :=
  Nonempty Λ ∧ (∀ i : Λ, ChosenBigFppfSite.IsAlgebraicSpace (D.obj i)) ∧
    (∀ {i j : Λ} (f : i ⟶ j),
      IsAffineFormalAlgebraicSpace.isRelativeThickening (D.map f)) ∧
      ∃ (c : Cocone D), Nonempty (IsColimit c) ∧ Nonempty (X ≅ c.pt)

/-- A directed algebraic-space thickening colimit presentation is equivalent
to nonempty indexing, algebraic-space stages, relative thickening transitions,
and a sheaf colimit isomorphic to `X`. -/
theorem isDirectedAlgebraicSpaceThickeningColimit_iff
    {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    {Λ : Type (max u v)} [Preorder Λ] [IsDirected Λ (· ≤ ·)]
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (D : Λ ⥤ Sheaf (𝒮.bigTopology S) (Type (max u v)))
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v))) :
    IsDirectedAlgebraicSpaceThickeningColimit D X ↔
      Nonempty Λ ∧ (∀ i : Λ, ChosenBigFppfSite.IsAlgebraicSpace (D.obj i)) ∧
        (∀ {i j : Λ} (f : i ⟶ j),
          IsAffineFormalAlgebraicSpace.isRelativeThickening (D.map f)) ∧
          ∃ (c : Cocone D), Nonempty (IsColimit c) ∧ Nonempty (X ≅ c.pt) := sorry

namespace IsDirectedAlgebraicSpaceThickeningColimit

/-- A directed algebraic-space thickening colimit has nonempty indexing,
algebraic-space stages, relative thickening transitions, and a sheaf colimit
isomorphic to `X`. -/
theorem spec {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    {Λ : Type (max u v)} [Preorder Λ] [IsDirected Λ (· ≤ ·)]
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    {D : Λ ⥤ Sheaf (𝒮.bigTopology S) (Type (max u v))}
    {X : Sheaf (𝒮.bigTopology S) (Type (max u v))}
    (h : IsDirectedAlgebraicSpaceThickeningColimit D X) :
    Nonempty Λ ∧ (∀ i : Λ, ChosenBigFppfSite.IsAlgebraicSpace (D.obj i)) ∧
      (∀ {i j : Λ} (f : i ⟶ j),
        IsAffineFormalAlgebraicSpace.isRelativeThickening (D.map f)) ∧
        ∃ (c : Cocone D), Nonempty (IsColimit c) ∧ Nonempty (X ≅ c.pt) := sorry

end IsDirectedAlgebraicSpaceThickeningColimit

namespace IsFormalAlgebraicSpace

/-- A nonempty directed colimit of algebraic spaces along relative thickenings
is a formal algebraic space, provided the colimit admits a coequalizer
presentation by representables from the same fixed chosen big fppf site.
The fixed-site presentation is supplied by `h_size`. -/
theorem of_directedAlgebraicSpaceColimit
    {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    {Λ : Type (max u v)} [Preorder Λ] [IsDirected Λ (· ≤ ·)] [Nonempty Λ]
    (F : Λ ⥤ Sheaf (𝒮.bigTopology S) (Type (max u v)))
    (h_algebraicSpace : ∀ i, ChosenBigFppfSite.IsAlgebraicSpace (F.obj i))
    (h_thickening : ∀ {i j : Λ} (f : i ⟶ j),
      IsAffineFormalAlgebraicSpace.isRelativeThickening (F.map f))
    (c : Cocone F) (hc : IsColimit c)
    (h_size : ChosenBigFppfSite.IsCoequalizerOfRepresentables c.pt) :
    IsFormalAlgebraicSpace c.pt := sorry

/-- A sheaf isomorphic to a nonempty directed colimit of algebraic spaces
along relative thickenings is a formal algebraic space, provided it admits
a coequalizer presentation by representables from the same fixed chosen big
fppf site. The fixed-site presentation is supplied by `h_size`. -/
theorem of_isDirectedAlgebraicSpaceThickeningColimit
    {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    {Λ : Type (max u v)} [Preorder Λ] [IsDirected Λ (· ≤ ·)]
    {D : Λ ⥤ Sheaf (𝒮.bigTopology S) (Type (max u v))}
    {X : Sheaf (𝒮.bigTopology S) (Type (max u v))}
    (h : IsDirectedAlgebraicSpaceThickeningColimit D X)
    (h_size : ChosenBigFppfSite.IsCoequalizerOfRepresentables X) :
    IsFormalAlgebraicSpace X := sorry

end IsFormalAlgebraicSpace

end AlgebraicGeometry
