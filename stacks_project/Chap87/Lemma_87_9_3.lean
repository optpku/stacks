/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.MorphismProperty.Representable
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Thickening
public import stacks_project.Chap87.Definition_87_9_1_Affine

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

namespace AlgebraicGeometry
namespace IsAffineFormalAlgebraicSpace

/-- Lemma 87.9.3 (1): Let `X_λ`, `λ ∈ Λ` and `X ≅ colim X_λ` be as in
Definition 87.9.1. Then the stage map `X_λ ⟶ X` of fppf sheaves is
representable. -/
@[stacks 0AI9]
theorem relativelyRepresentable_stageι {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    {Λ : Type (max u v)} [Preorder Λ] [IsDirected Λ (· ≤ ·)]
    (D : Λ ⥤ 𝒮.bigAffineSite S) (X : Sheaf (𝒮.bigTopology S) (Type (max u v)))
    [IsAffineFormalAlgebraicSpace X] (hD : IsDirectedAffineThickeningColimit D X)
    (c : Cocone
      (D ⋙ 𝒮.bigAffineInclusion S ⋙ (𝒮.bigTopology S).sheafifiedRepresentableFunctor))
    (hc : IsColimit c) (e : X ≅ c.pt) (i : Λ) :
    (𝒮.bigTopology S).sheafifiedRepresentableFunctor.relativelyRepresentable
      (c.ι.app i ≫ e.inv) :=
  sorry

/-- Lemma 87.9.3 (2): Let `X_λ`, `λ ∈ Λ` and `X ≅ colim X_λ` be as in
Definition 87.9.1. Then the stage map `X_λ ⟶ X` of fppf sheaves is a
thickening. -/
@[stacks 0AI9]
theorem isThickening_stageι {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    {Λ : Type (max u v)} [Preorder Λ] [IsDirected Λ (· ≤ ·)]
    (D : Λ ⥤ 𝒮.bigAffineSite S) (X : Sheaf (𝒮.bigTopology S) (Type (max u v)))
    [IsAffineFormalAlgebraicSpace X] (hD : IsDirectedAffineThickeningColimit D X)
    (c : Cocone
      (D ⋙ 𝒮.bigAffineInclusion S ⋙ (𝒮.bigTopology S).sheafifiedRepresentableFunctor))
    (hc : IsColimit c) (e : X ≅ c.pt) (i : Λ) :
    (MorphismProperty.inverseImage (@IsThickening) (𝒮.bigToScheme S)).relative
      (𝒮.bigTopology S).sheafifiedRepresentableFunctor (c.ι.app i ≫ e.inv) :=
  sorry

/-- Relative thickening of a stage map unpacks as relative representability
together with thickenings of represented pullbacks on source schemes. -/
theorem isThickening_stageι_spec {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    {Λ : Type (max u v)} [Preorder Λ] [IsDirected Λ (· ≤ ·)]
    (D : Λ ⥤ 𝒮.bigAffineSite S) (X : Sheaf (𝒮.bigTopology S) (Type (max u v)))
    [IsAffineFormalAlgebraicSpace X] (hD : IsDirectedAffineThickeningColimit D X)
    (c : Cocone
      (D ⋙ 𝒮.bigAffineInclusion S ⋙ (𝒮.bigTopology S).sheafifiedRepresentableFunctor))
    (hc : IsColimit c) (e : X ≅ c.pt) (i : Λ) :
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
          IsThickening ((𝒮.bigToScheme S).map snd) :=
  sorry

end IsAffineFormalAlgebraicSpace
end AlgebraicGeometry
