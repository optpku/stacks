/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Pullback
public import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

universe u v

namespace AlgebraicGeometry.Scheme.Etale

/-- The small étale inverse-image presheaf of a sheaf `𝒢` along `f : X ⟶ Y`,
evaluated at `U : X.Etale`, is the colimit of `𝒢` over the costructured-arrow
category of small étale base change at `op U`. -/
theorem smallEtaleInverseImagePresheaf_obj {X Y : Scheme.{u}} (f : X ⟶ Y)
    (𝒢 : Sheaf Y.smallEtaleTopology (Type v))
    [((smallEtalePullback f).op).HasPointwiseLeftKanExtension 𝒢.1]
    (U : X.Etale) :
    (Functor.pointwiseLeftKanExtension ((smallEtalePullback f).op) 𝒢.1).obj (op U) =
      colimit (CostructuredArrow.proj ((smallEtalePullback f).op) (op U) ⋙ 𝒢.1) := sorry

end AlgebraicGeometry.Scheme.Etale
