/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap87.Definition_87_11_1_Formal
public import stacks_project.Chap87.Lemma_87_17_1_QuasiCompact

/-!
# Quasi-separated formal algebraic spaces

A formal algebraic space is quasi-separated when maps from sheafified affine
representables have quasi-compact fibre product, equivalently when the
reduction is a quasi-separated algebraic space.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.GrothendieckTopology
open AlgebraicGeometry.ChosenBigFppfSite

noncomputable section

universe u v

namespace AlgebraicGeometry

/-- A sheaf on `(Sch/S)_fppf` is a quasi-separated formal algebraic space when
it is a formal algebraic space and affine tests have quasi-compact fibre
product. -/
class IsQuasiSeparatedFormalAlgebraicSpace {𝒮 : ChosenBigFppfSite.{u, v}}
    {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v))) : Prop
    extends IsFormalAlgebraicSpace X where
  /-- For maps from sheafified affine representables, the fibre product is a
  quasi-compact algebraic space. -/
  quasiCompact_affine_fibre_product
      {U V : 𝒮.bigAffineSite S}
      (u : (𝒮.bigTopology S).sheafifiedRepresentable
        ((𝒮.bigAffineInclusion S).obj U) ⟶ X)
      (v : (𝒮.bigTopology S).sheafifiedRepresentable
        ((𝒮.bigAffineInclusion S).obj V) ⟶ X) :
      ChosenBigFppfSite.IsQuasiCompact (pullback u v)

namespace IsQuasiSeparatedFormalAlgebraicSpace

/-- The sheafified representable of an affine object of `(Sch/S)_fppf` is a
quasi-separated formal algebraic space. -/
instance instSheafifiedRepresentable {𝒮 : ChosenBigFppfSite.{u, v}}
    {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (U : 𝒮.bigAffineSite S) :
    IsQuasiSeparatedFormalAlgebraicSpace
      ((𝒮.bigTopology S).sheafifiedRepresentable
        ((𝒮.bigAffineInclusion S).obj U)) :=
  sorry

/-- A sheaf is a quasi-separated formal algebraic space iff it is a formal
algebraic space and affine tests have quasi-compact fibre product. -/
theorem iff {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v))) :
    IsQuasiSeparatedFormalAlgebraicSpace X ↔
      IsFormalAlgebraicSpace X ∧
        ∀ (U V : 𝒮.bigAffineSite S)
          (u : (𝒮.bigTopology S).sheafifiedRepresentable
            ((𝒮.bigAffineInclusion S).obj U) ⟶ X)
          (v : (𝒮.bigTopology S).sheafifiedRepresentable
            ((𝒮.bigAffineInclusion S).obj V) ⟶ X),
          ChosenBigFppfSite.IsQuasiCompact (pullback u v) :=
  sorry

/-- A quasi-separated formal algebraic space unpacks as affine tests having
quasi-compact fibre product. -/
theorem spec {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v)))
    [IsQuasiSeparatedFormalAlgebraicSpace X]
    {U V : 𝒮.bigAffineSite S}
    (u : (𝒮.bigTopology S).sheafifiedRepresentable
      ((𝒮.bigAffineInclusion S).obj U) ⟶ X)
    (v : (𝒮.bigTopology S).sheafifiedRepresentable
      ((𝒮.bigAffineInclusion S).obj V) ⟶ X) :
    ChosenBigFppfSite.IsQuasiCompact (pullback u v) :=
  sorry

end IsQuasiSeparatedFormalAlgebraicSpace

end AlgebraicGeometry
