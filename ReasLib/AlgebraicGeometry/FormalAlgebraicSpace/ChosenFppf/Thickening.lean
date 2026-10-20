module

public import Mathlib.CategoryTheory.MorphismProperty.Representable
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Fppf.ChosenPresentation
public import ReasLib.CategoryTheory.Sites.SheafifiedRepresentable
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Thickening
public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.ChosenFppf.Affine

/-!
# Relative thickenings on a chosen big fppf site

Relative thickenings are relatively representable morphisms of sheaves whose
represented pullbacks are thickenings of schemes.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.GrothendieckTopology
open AlgebraicGeometry.ChosenBigFppfSite

noncomputable section

universe u v

namespace AlgebraicGeometry
namespace IsAffineFormalAlgebraicSpace

/-- A morphism of fppf sheaves is a relative thickening when it is relatively
representable and every represented pullback is a thickening of schemes. -/
def isRelativeThickening {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    {X Y : Sheaf (𝒮.bigTopology S) (Type (max u v))} (f : X ⟶ Y) : Prop :=
  (MorphismProperty.inverseImage (@IsThickening) (𝒮.bigToScheme S)).relative
    (𝒮.bigTopology S).sheafifiedRepresentableFunctor f

/-- Relative thickening unpacks as relative representability together with
thickenings of represented pullbacks on source schemes, i.e. closed immersions
inducing isomorphisms on scheme reductions. -/
theorem isRelativeThickening_iff {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    {X Y : Sheaf (𝒮.bigTopology S) (Type (max u v))} (f : X ⟶ Y) :
    isRelativeThickening f ↔
      (𝒮.bigTopology S).sheafifiedRepresentableFunctor.relativelyRepresentable f ∧
        ∀ {U V : 𝒮.bigSite S}
          (ξ : (𝒮.bigTopology S).sheafifiedRepresentable U ⟶ Y)
          (fst : (𝒮.bigTopology S).sheafifiedRepresentable V ⟶ X) (snd : V ⟶ U),
          IsPullback fst ((𝒮.bigTopology S).sheafifiedRepresentableMap snd) f ξ →
            IsThickening ((𝒮.bigToScheme S).map snd) :=
  sorry

/-- Every stage map of a directed affine thickening presentation of an affine
formal algebraic space is a relative thickening of fppf sheaves. -/
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

/-- Every stage map of a directed affine thickening presentation of an affine
formal algebraic space is relatively representable. -/
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
  (isThickening_stageι D X hD c hc e i).1

/-- A stage map of a directed affine thickening presentation is relatively
representable, and every represented pullback is a thickening of schemes. -/
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
  isThickening_stageι D X hD c hc e i

end IsAffineFormalAlgebraicSpace
end AlgebraicGeometry
