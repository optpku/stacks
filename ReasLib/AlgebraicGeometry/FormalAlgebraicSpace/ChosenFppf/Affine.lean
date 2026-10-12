/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.Order.Directed
public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.ChosenFppf.Size
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Thickening

/-!
# Affine formal algebraic spaces on a chosen big fppf site

Affine formal algebraic spaces are represented by directed systems of affine
objects with thickening transitions and satisfy the fixed-site presentation
condition.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.GrothendieckTopology
open AlgebraicGeometry.ChosenBigFppfSite

noncomputable section

universe u v

namespace AlgebraicGeometry

/-- A diagram of affine objects with thickening transitions has sheaf colimit
isomorphic to `X`. -/
def IsDirectedAffineThickeningColimit
    {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    {Λ : Type (max u v)} [Preorder Λ] [IsDirected Λ (· ≤ ·)]
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    (D : Λ ⥤ 𝒮.bigAffineSite S)
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v))) : Prop :=
  Nonempty Λ ∧
    (∀ {i j : Λ} (f : i ⟶ j),
        IsThickening ((𝒮.bigAffineToScheme S).map (D.map f))) ∧
      ∃ (c : Cocone
          (D ⋙ 𝒮.bigAffineInclusion S ⋙
            (𝒮.bigTopology S).sheafifiedRepresentableFunctor)),
        Nonempty (IsColimit c) ∧ Nonempty (X ≅ c.pt)

/-- The directed affine thickening colimit predicate is equivalent to its
explicit transition and colimit specification. -/
theorem IsDirectedAffineThickeningColimit_iff
    {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    {Λ : Type (max u v)} [Preorder Λ] [IsDirected Λ (· ≤ ·)]
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    (D : Λ ⥤ 𝒮.bigAffineSite S)
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v))) :
    IsDirectedAffineThickeningColimit D X ↔
      Nonempty Λ ∧
        (∀ {i j : Λ} (f : i ⟶ j),
            IsThickening ((𝒮.bigAffineToScheme S).map (D.map f))) ∧
          ∃ (c : Cocone
              (D ⋙ 𝒮.bigAffineInclusion S ⋙
                (𝒮.bigTopology S).sheafifiedRepresentableFunctor)),
            Nonempty (IsColimit c) ∧ Nonempty (X ≅ c.pt) := sorry

/-- A sheaf on the chosen big fppf site is an affine formal algebraic space if
it is a directed affine thickening colimit satisfying the fixed-site
presentation condition. -/
class IsAffineFormalAlgebraicSpace
    {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v))) : Prop
    extends IsCoequalizerOfRepresentables X where
  /-- There exist a directed set and a diagram of affine objects with thickening
  transitions whose sheaf colimit is isomorphic to `X`. -/
  exists_colimit :
    ∃ (Λ : Type (max u v)) (_ : Preorder Λ) (_ : IsDirected Λ (· ≤ ·))
      (D : Λ ⥤ 𝒮.bigAffineSite S),
        IsDirectedAffineThickeningColimit D X

namespace IsAffineFormalAlgebraicSpace

/-- The sheafified representable of an affine object is an affine formal
algebraic space. -/
instance instSheafifiedRepresentable {𝒮 : ChosenBigFppfSite.{u, v}}
    {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (U : 𝒮.bigAffineSite S) :
    IsAffineFormalAlgebraicSpace
      ((𝒮.bigTopology S).sheafifiedRepresentable
        ((𝒮.bigAffineInclusion S).obj U)) := sorry

/-- The affine formal algebraic space condition is equivalent to the directed
colimit and fixed-site presentation conditions. -/
theorem iff {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v))) :
    IsAffineFormalAlgebraicSpace X ↔
      (∃ (Λ : Type (max u v)) (_ : Preorder Λ) (_ : IsDirected Λ (· ≤ ·))
          (D : Λ ⥤ 𝒮.bigAffineSite S),
            IsDirectedAffineThickeningColimit D X) ∧
        IsCoequalizerOfRepresentables X := sorry

/-- An affine formal algebraic space admits the directed-system and fixed-site
presentation data appearing in its definition. -/
theorem spec {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v)))
    [IsAffineFormalAlgebraicSpace X] :
    ∃ (Λ : Type (max u v)) (_ : Preorder Λ) (_ : IsDirected Λ (· ≤ ·))
      (D : Λ ⥤ 𝒮.bigAffineSite S),
        Nonempty Λ ∧
          (∀ i, IsAffine ((𝒮.bigAffineToScheme S).obj (D.obj i))) ∧
            (∀ {i j : Λ} (f : i ⟶ j),
                IsThickening ((𝒮.bigAffineToScheme S).map (D.map f))) ∧
              (∃ (c : Cocone
                  (D ⋙ 𝒮.bigAffineInclusion S ⋙
                    (𝒮.bigTopology S).sheafifiedRepresentableFunctor)),
                Nonempty (IsColimit c) ∧ Nonempty (X ≅ c.pt)) ∧
                ∃ (U R : 𝒮.bigSite S)
                  (π : (𝒮.bigTopology S).sheafifiedRepresentable U ⟶ X)
                  (σ : (𝒮.bigTopology S).sheafifiedRepresentable R ⟶
                    pullback π π),
                    Sheaf.IsLocallySurjective π ∧
                      Sheaf.IsLocallySurjective σ := sorry

end IsAffineFormalAlgebraicSpace

end AlgebraicGeometry
