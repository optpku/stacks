module

public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.CategoryTheory.MorphismProperty.Representable
public import Mathlib.Order.Directed
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Thickening
public import stacks_project.Chap87.Definition_87_11_1_Representable

/-!
# Directed algebraic-space thickening colimits

A sheaf on `(Sch/S)_fppf` is a directed colimit of algebraic spaces along
thickening transitions when the stages are algebraic spaces, each transition
is a relative thickening, and the sheaf is isomorphic to a colimit cocone.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.GrothendieckTopology
open AlgebraicGeometry.ChosenBigFppfSite

noncomputable section

universe u v

namespace AlgebraicGeometry

/-- A directed diagram of algebraic-space sheaves with thickening transitions
has sheaf colimit isomorphic to `X`. -/
def IsDirectedAlgebraicSpaceThickeningColimit
    {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    {Λ : Type (max u v)} [Preorder Λ] [IsDirected Λ (· ≤ ·)]
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (D : Λ ⥤ Sheaf (𝒮.bigTopology S) (Type (max u v)))
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v))) : Prop :=
  (∀ i : Λ, ChosenBigFppfSite.IsAlgebraicSpace (D.obj i)) ∧
    (∀ {i j : Λ} (f : i ⟶ j),
      (MorphismProperty.inverseImage (@IsThickening) (𝒮.bigToScheme S)).relative
        (𝒮.bigTopology S).sheafifiedRepresentableFunctor (D.map f)) ∧
      ∃ (c : Cocone D), Nonempty (IsColimit c) ∧ Nonempty (X ≅ c.pt)

/-- The directed algebraic-space thickening colimit predicate unpacks as
algebraic-space stages, relative thickening transitions, and a sheaf colimit
isomorphic to `X`. -/
theorem IsDirectedAlgebraicSpaceThickeningColimit_iff
    {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    {Λ : Type (max u v)} [Preorder Λ] [IsDirected Λ (· ≤ ·)]
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (D : Λ ⥤ Sheaf (𝒮.bigTopology S) (Type (max u v)))
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v))) :
    IsDirectedAlgebraicSpaceThickeningColimit D X ↔
      (∀ i : Λ, ChosenBigFppfSite.IsAlgebraicSpace (D.obj i)) ∧
        (∀ {i j : Λ} (f : i ⟶ j),
          (MorphismProperty.inverseImage (@IsThickening)
            (𝒮.bigToScheme S)).relative
            (𝒮.bigTopology S).sheafifiedRepresentableFunctor (D.map f)) ∧
          ∃ (c : Cocone D), Nonempty (IsColimit c) ∧ Nonempty (X ≅ c.pt) :=
  sorry

namespace IsDirectedAlgebraicSpaceThickeningColimit

/-- A directed algebraic-space thickening colimit has algebraic-space stages,
relative thickening transitions, and a sheaf colimit isomorphic to `X`. -/
theorem spec {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    {Λ : Type (max u v)} [Preorder Λ] [IsDirected Λ (· ≤ ·)]
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    {D : Λ ⥤ Sheaf (𝒮.bigTopology S) (Type (max u v))}
    {X : Sheaf (𝒮.bigTopology S) (Type (max u v))}
    (h : IsDirectedAlgebraicSpaceThickeningColimit D X) :
    (∀ i : Λ, ChosenBigFppfSite.IsAlgebraicSpace (D.obj i)) ∧
      (∀ {i j : Λ} (f : i ⟶ j),
        (MorphismProperty.inverseImage (@IsThickening)
          (𝒮.bigToScheme S)).relative
          (𝒮.bigTopology S).sheafifiedRepresentableFunctor (D.map f)) ∧
        ∃ (c : Cocone D), Nonempty (IsColimit c) ∧ Nonempty (X ≅ c.pt) :=
  sorry

end IsDirectedAlgebraicSpaceThickeningColimit

end AlgebraicGeometry
