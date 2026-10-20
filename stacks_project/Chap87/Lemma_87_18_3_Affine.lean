/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import stacks_project.Chap87.Definition_87_11_1_Representable

/-!
# Affine algebraic spaces on a chosen big fppf site

A sheaf on `(Sch/S)_fppf` is an affine algebraic space when it is an algebraic
space isomorphic to the sheafified representable of an affine object of the
site.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.GrothendieckTopology
open AlgebraicGeometry.ChosenBigFppfSite

noncomputable section

universe u v

namespace AlgebraicGeometry.ChosenBigFppfSite

/-- A sheaf on `(Sch/S)_fppf` is an affine algebraic space when it is an
algebraic space isomorphic to the sheafified representable of an affine object
of the site. -/
class IsAffine {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v))) : Prop
    extends IsAlgebraicSpace X where
  /-- There is an affine object of `(Sch/S)_fppf` whose sheafified
  representable is isomorphic to `X`. -/
  exists_affine :
    ∃ (U : 𝒮.bigSite S),
      AlgebraicGeometry.IsAffine ((𝒮.bigToScheme S).obj U) ∧
        Nonempty (X ≅ (𝒮.bigTopology S).sheafifiedRepresentable U)

/-- The sheafified representable of an affine object of `(Sch/S)_fppf` is an
affine algebraic space. -/
instance instIsAffine_sheafifiedRepresentable
    {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (U : 𝒮.bigSite S)
    [hU : AlgebraicGeometry.IsAffine ((𝒮.bigToScheme S).obj U)] :
    IsAffine ((𝒮.bigTopology S).sheafifiedRepresentable U) where
  exists_affine :=
    ⟨U, hU, ⟨Iso.refl ((𝒮.bigTopology S).sheafifiedRepresentable U)⟩⟩

namespace IsAffine

/-- A sheaf is an affine algebraic space iff it is an algebraic space
isomorphic to the sheafified representable of an affine object of the site. -/
theorem iff {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v))) :
    IsAffine X ↔
      IsAlgebraicSpace X ∧
        ∃ (U : 𝒮.bigSite S),
          AlgebraicGeometry.IsAffine ((𝒮.bigToScheme S).obj U) ∧
            Nonempty (X ≅ (𝒮.bigTopology S).sheafifiedRepresentable U) :=
  sorry

/-- An affine algebraic space unpacks as an algebraic space together with an
isomorphism to the sheafified representable of an affine object of the site. -/
theorem spec {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v))) [IsAffine X] :
    IsAlgebraicSpace X ∧
      ∃ (U : 𝒮.bigSite S),
        AlgebraicGeometry.IsAffine ((𝒮.bigToScheme S).obj U) ∧
          Nonempty (X ≅ (𝒮.bigTopology S).sheafifiedRepresentable U) :=
  sorry

/-- An isomorphism with the sheafified representable of an affine object of
`(Sch/S)_fppf` witnesses that an algebraic space is affine. -/
theorem of {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    {X : Sheaf (𝒮.bigTopology S) (Type (max u v))} [IsAlgebraicSpace X]
    {U : 𝒮.bigSite S}
    [AlgebraicGeometry.IsAffine ((𝒮.bigToScheme S).obj U)]
    (e : X ≅ (𝒮.bigTopology S).sheafifiedRepresentable U) : IsAffine X :=
  sorry

end IsAffine

end AlgebraicGeometry.ChosenBigFppfSite
