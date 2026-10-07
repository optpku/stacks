module

public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.Order.Directed
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Thickening
public import stacks_project.Chap87.Definition_87_9_1_SetTheoretic

/-!
# Affine formal algebraic spaces

A sheaf on the fixed big fppf site `(Sch/S)_fppf` is an affine formal algebraic
space when it is isomorphic, as an fppf sheaf, to a directed colimit of affine
objects along thickening transitions, and it satisfies the coequalizer size
condition on that same site.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.GrothendieckTopology
open AlgebraicGeometry.ChosenBigFppfSite

noncomputable section

universe u v

namespace AlgebraicGeometry

/-- A diagram of affine objects of `(Sch/S)_fppf` with thickening transitions has
sheaf colimit isomorphic to `X`. -/
def IsDirectedAffineThickeningColimit
    {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    {Λ : Type (max u v)} [Preorder Λ] [IsDirected Λ (· ≤ ·)]
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    (D : Λ ⥤ 𝒮.bigAffineSite S)
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v))) : Prop :=
  (∀ {i j : Λ} (f : i ⟶ j),
      IsThickening ((𝒮.bigAffineToScheme S).map (D.map f))) ∧
    ∃ (c : Cocone
        (D ⋙ 𝒮.bigAffineInclusion S ⋙
          (𝒮.bigTopology S).sheafifiedRepresentableFunctor)),
      Nonempty (IsColimit c) ∧ Nonempty (X ≅ c.pt)

/-- The directed affine thickening colimit predicate unpacks as thickening
transitions together with a sheaf colimit isomorphic to `X`. -/
theorem IsDirectedAffineThickeningColimit_iff
    {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    {Λ : Type (max u v)} [Preorder Λ] [IsDirected Λ (· ≤ ·)]
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    (D : Λ ⥤ 𝒮.bigAffineSite S)
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v))) :
    IsDirectedAffineThickeningColimit D X ↔
      (∀ {i j : Λ} (f : i ⟶ j),
          IsThickening ((𝒮.bigAffineToScheme S).map (D.map f))) ∧
        ∃ (c : Cocone
            (D ⋙ 𝒮.bigAffineInclusion S ⋙
              (𝒮.bigTopology S).sheafifiedRepresentableFunctor)),
          Nonempty (IsColimit c) ∧ Nonempty (X ≅ c.pt) := sorry

/-- A sheaf on `(Sch/S)_fppf` is an affine formal algebraic space when it is a
directed colimit of affine objects along thickening transitions and is a
coequalizer of two maps of representable sheaves on the same fixed site. -/
class IsAffineFormalAlgebraicSpace
    {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v))) : Prop
    extends IsCoequalizerOfRepresentables X where
  /-- There exist a directed set and a system of affine objects of
  `(Sch/S)_fppf` with thickening transitions whose fppf-sheaf colimit is
  isomorphic to `X`. -/
  exists_colimit :
    ∃ (Λ : Type (max u v)) (_ : Preorder Λ) (_ : IsDirected Λ (· ≤ ·))
      (D : Λ ⥤ 𝒮.bigAffineSite S),
        IsDirectedAffineThickeningColimit D X

namespace IsAffineFormalAlgebraicSpace

/-- The sheafified representable of an affine object of `(Sch/S)_fppf` is an
affine formal algebraic space, via the constant directed system. -/
instance instSheafifiedRepresentable {𝒮 : ChosenBigFppfSite.{u, v}}
    {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (U : 𝒮.bigAffineSite S) :
    IsAffineFormalAlgebraicSpace
      ((𝒮.bigTopology S).sheafifiedRepresentable
        ((𝒮.bigAffineInclusion S).obj U)) := sorry

/-- An affine formal algebraic space is a directed affine thickening colimit
satisfying the coequalizer size condition. -/
theorem iff {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v))) :
    IsAffineFormalAlgebraicSpace X ↔
      (∃ (Λ : Type (max u v)) (_ : Preorder Λ) (_ : IsDirected Λ (· ≤ ·))
          (D : Λ ⥤ 𝒮.bigAffineSite S),
            IsDirectedAffineThickeningColimit D X) ∧
        IsCoequalizerOfRepresentables X := sorry

/-- An affine formal algebraic space unpacks as a directed set of affine objects
of `(Sch/S)_fppf`, thickening transitions, a sheaf colimit isomorphism, and
objects `U`, `R` of the same site with surjections `U ⟶ X` and
`R ⟶ U ×_X U`. -/
theorem spec {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v)))
    [IsAffineFormalAlgebraicSpace X] :
    ∃ (Λ : Type (max u v)) (_ : Preorder Λ) (_ : IsDirected Λ (· ≤ ·))
      (D : Λ ⥤ 𝒮.bigAffineSite S),
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
