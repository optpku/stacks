/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.ChosenFppf.Affine
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ChosenFppf

/-!
# Affine morphisms of affine formal algebraic spaces

A morphism between affine formal algebraic spaces on a chosen big fppf site
that is representable by algebraic spaces is representable by schemes and affine.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.GrothendieckTopology
open AlgebraicGeometry.ChosenBigFppfSite

noncomputable section

universe u v

namespace AlgebraicGeometry
namespace IsAffineFormalAlgebraicSpace

/-- A morphism between affine formal algebraic spaces that is representable by
algebraic spaces is representable by schemes and affine. -/
theorem isAffineHom_relative {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    {X Y : Sheaf (𝒮.bigTopology S) (Type (max u v))}
    [IsAffineFormalAlgebraicSpace X] [IsAffineFormalAlgebraicSpace Y]
    {f : X ⟶ Y} (hf : representableByAlgebraicSpaces f) :
    (MorphismProperty.inverseImage (@IsAffineHom) (𝒮.bigToScheme S)).relative
      (𝒮.bigTopology S).sheafifiedRepresentableFunctor f :=
  sorry

end IsAffineFormalAlgebraicSpace
end AlgebraicGeometry
