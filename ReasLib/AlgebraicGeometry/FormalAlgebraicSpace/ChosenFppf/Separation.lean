/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ChosenFppf.Separation
public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.ChosenFppf.Basic

/-!
# Separated formal algebraic spaces

A formal algebraic space is separated when maps from sheafified affine
representables have affine fibre product and the induced section tensor
`Γ(U, ⊤) ⊗[ℤ] Γ(V, ⊤) →+* Γ(W, ⊤)` is surjective.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.GrothendieckTopology
open AlgebraicGeometry.ChosenBigFppfSite
open scoped TensorProduct

noncomputable section

universe u v

namespace AlgebraicGeometry

/-- A sheaf on `(Sch/S)_fppf` is a separated formal algebraic space when it is a
formal algebraic space and affine tests have affine fibre product with
surjective section tensor. -/
class IsSeparatedFormalAlgebraicSpace {𝒮 : ChosenBigFppfSite.{u, v}}
    {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v))) : Prop
    extends IsFormalAlgebraicSpace X where
  /-- For maps from sheafified affine representables, the fibre product is
  affine and the section tensor is surjective. -/
  affine_fibre_product_surjective_section_tensor
      {U V : 𝒮.bigAffineSite S}
      (u : (𝒮.bigTopology S).sheafifiedRepresentable
        ((𝒮.bigAffineInclusion S).obj U) ⟶ X)
      (v : (𝒮.bigTopology S).sheafifiedRepresentable
        ((𝒮.bigAffineInclusion S).obj V) ⟶ X) :
      ∃ (W : 𝒮.bigAffineSite S) (p : W ⟶ U) (q : W ⟶ V)
        (e : pullback u v ≅ (𝒮.bigTopology S).sheafifiedRepresentable
          ((𝒮.bigAffineInclusion S).obj W)),
        e.hom ≫ (𝒮.bigTopology S).sheafifiedRepresentableMap
            ((𝒮.bigAffineInclusion S).map p) =
          pullback.fst u v ∧
        e.hom ≫ (𝒮.bigTopology S).sheafifiedRepresentableMap
            ((𝒮.bigAffineInclusion S).map q) =
          pullback.snd u v ∧
        Function.Surjective (sectionTensor p q)

namespace IsSeparatedFormalAlgebraicSpace

/-- The sheafified representable of an affine object of `(Sch/S)_fppf` is a
separated formal algebraic space. -/
instance instSheafifiedRepresentable {𝒮 : ChosenBigFppfSite.{u, v}}
    {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (U : 𝒮.bigAffineSite S) :
    IsSeparatedFormalAlgebraicSpace
      ((𝒮.bigTopology S).sheafifiedRepresentable
        ((𝒮.bigAffineInclusion S).obj U)) := sorry

/-- A sheaf is a separated formal algebraic space iff it is a formal algebraic
space and affine tests have affine fibre product with surjective section
tensor. -/
theorem iff {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v))) :
    IsSeparatedFormalAlgebraicSpace X ↔
      IsFormalAlgebraicSpace X ∧
        ∀ (U V : 𝒮.bigAffineSite S)
          (u : (𝒮.bigTopology S).sheafifiedRepresentable
            ((𝒮.bigAffineInclusion S).obj U) ⟶ X)
          (v : (𝒮.bigTopology S).sheafifiedRepresentable
            ((𝒮.bigAffineInclusion S).obj V) ⟶ X),
          ∃ (W : 𝒮.bigAffineSite S) (p : W ⟶ U) (q : W ⟶ V)
            (e : pullback u v ≅ (𝒮.bigTopology S).sheafifiedRepresentable
              ((𝒮.bigAffineInclusion S).obj W)),
            e.hom ≫ (𝒮.bigTopology S).sheafifiedRepresentableMap
                ((𝒮.bigAffineInclusion S).map p) =
              pullback.fst u v ∧
            e.hom ≫ (𝒮.bigTopology S).sheafifiedRepresentableMap
                ((𝒮.bigAffineInclusion S).map q) =
              pullback.snd u v ∧
            Function.Surjective (sectionTensor p q) := sorry

/-- A separated formal algebraic space unpacks as affine tests having affine
fibre product with surjective section tensor. -/
theorem spec {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v)))
    [IsSeparatedFormalAlgebraicSpace X]
    {U V : 𝒮.bigAffineSite S}
    (u : (𝒮.bigTopology S).sheafifiedRepresentable
      ((𝒮.bigAffineInclusion S).obj U) ⟶ X)
    (v : (𝒮.bigTopology S).sheafifiedRepresentable
      ((𝒮.bigAffineInclusion S).obj V) ⟶ X) :
    ∃ (W : 𝒮.bigAffineSite S) (p : W ⟶ U) (q : W ⟶ V)
      (e : pullback u v ≅ (𝒮.bigTopology S).sheafifiedRepresentable
        ((𝒮.bigAffineInclusion S).obj W)),
      e.hom ≫ (𝒮.bigTopology S).sheafifiedRepresentableMap
          ((𝒮.bigAffineInclusion S).map p) =
        pullback.fst u v ∧
      e.hom ≫ (𝒮.bigTopology S).sheafifiedRepresentableMap
          ((𝒮.bigAffineInclusion S).map q) =
        pullback.snd u v ∧
      Function.Surjective (sectionTensor p q) := sorry

/-- A sheaf is a separated formal algebraic space iff it is a formal algebraic
space and affine tests have affine fibre product with surjective
`sectionTensor`. -/
theorem iff_forallAffinePullbackAffineSurjective
    {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v))) :
    IsSeparatedFormalAlgebraicSpace X ↔
      IsFormalAlgebraicSpace X ∧ forallAffinePullbackAffineSurjective X := sorry


end IsSeparatedFormalAlgebraicSpace

end AlgebraicGeometry
