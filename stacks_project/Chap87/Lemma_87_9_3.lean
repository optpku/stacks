/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.ChosenFppf.Thickening
import StacksCheckRecall

/-!
# Lemma 87.9.3

Each stage map of a directed affine thickening presentation of an affine
formal algebraic space is representable and a thickening in the relative
representable-property sense.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.GrothendieckTopology
open AlgebraicGeometry.ChosenBigFppfSite

noncomputable section

universe u v

open AlgebraicGeometry

/- Lemma 87.9.3. Every stage map of a directed affine thickening presentation
of an affine formal algebraic space is representable and a thickening. -/
@[stacks 0AI9] #check (AlgebraicGeometry.IsAffineFormalAlgebraicSpace.isThickening_stageι :
  ∀ {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    {Λ : Type (max u v)} [Preorder Λ] [IsDirected Λ (· ≤ ·)]
    (D : Λ ⥤ 𝒮.bigAffineSite S) (X : Sheaf (𝒮.bigTopology S) (Type (max u v)))
    [IsAffineFormalAlgebraicSpace X] (hD : IsDirectedAffineThickeningColimit D X)
    (c : Cocone
      (D ⋙ 𝒮.bigAffineInclusion S ⋙ (𝒮.bigTopology S).sheafifiedRepresentableFunctor))
    (hc : IsColimit c) (e : X ≅ c.pt) (i : Λ),
    (MorphismProperty.inverseImage (@IsThickening) (𝒮.bigToScheme S)).relative
      (𝒮.bigTopology S).sheafifiedRepresentableFunctor (c.ι.app i ≫ e.inv))

#check (AlgebraicGeometry.IsAffineFormalAlgebraicSpace.relativelyRepresentable_stageι :
  ∀ {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    {Λ : Type (max u v)} [Preorder Λ] [IsDirected Λ (· ≤ ·)]
    (D : Λ ⥤ 𝒮.bigAffineSite S) (X : Sheaf (𝒮.bigTopology S) (Type (max u v)))
    [IsAffineFormalAlgebraicSpace X] (hD : IsDirectedAffineThickeningColimit D X)
    (c : Cocone
      (D ⋙ 𝒮.bigAffineInclusion S ⋙ (𝒮.bigTopology S).sheafifiedRepresentableFunctor))
    (hc : IsColimit c) (e : X ≅ c.pt) (i : Λ),
    (𝒮.bigTopology S).sheafifiedRepresentableFunctor.relativelyRepresentable
      (c.ι.app i ≫ e.inv))

#check (AlgebraicGeometry.IsAffineFormalAlgebraicSpace.isThickening_stageι_spec :
  ∀ {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    {Λ : Type (max u v)} [Preorder Λ] [IsDirected Λ (· ≤ ·)]
    (D : Λ ⥤ 𝒮.bigAffineSite S) (X : Sheaf (𝒮.bigTopology S) (Type (max u v)))
    [IsAffineFormalAlgebraicSpace X] (hD : IsDirectedAffineThickeningColimit D X)
    (c : Cocone
      (D ⋙ 𝒮.bigAffineInclusion S ⋙ (𝒮.bigTopology S).sheafifiedRepresentableFunctor))
    (hc : IsColimit c) (e : X ≅ c.pt) (i : Λ),
    (𝒮.bigTopology S).sheafifiedRepresentableFunctor.relativelyRepresentable
      (c.ι.app i ≫ e.inv) ∧
      ∀ {U V : 𝒮.bigSite S}
        (ξ : (𝒮.bigTopology S).sheafifiedRepresentable U ⟶ X)
        (fst : (𝒮.bigTopology S).sheafifiedRepresentable V ⟶
          (𝒮.bigTopology S).sheafifiedRepresentable
            ((𝒮.bigAffineInclusion S).obj (D.obj i)))
        (snd : V ⟶ U),
        IsPullback fst ((𝒮.bigTopology S).sheafifiedRepresentableMap snd)
          (c.ι.app i ≫ e.inv) ξ →
          IsThickening ((𝒮.bigToScheme S).map snd))
