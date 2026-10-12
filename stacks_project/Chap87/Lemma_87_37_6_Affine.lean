/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.Sites.LocallyInjective
public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import Mathlib.Order.Directed
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Thickening
public import stacks_project.Chap87.Lemma_87_37_4_Completion

/-!
# Affine formal algebraic spaces, functor of points

A functor of points `(Over S)ᵒᵖ ⥤ Type u` is an affine formal algebraic space
when it is a directed affine thickening colimit and satisfies the coequalizer
size condition.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.FormalAlgebraicSpace Opposite

noncomputable section

universe u v

namespace AlgebraicGeometry.AffineFormalAlgebraicSpace

/-- A diagram of schemes over `S` is a directed affine thickening colimit of `X`
when its objects are affine, its transitions are thickenings, `X` is an fppf
sheaf, and the comparison map from the Yoneda presheaf colimit of the diagram
to `X` is an fppf-local isomorphism. -/
class IsDirectedAffineThickeningColimit {S : Scheme.{u}} {Λ : Type v} [Preorder Λ]
    [IsDirected Λ (· ≤ ·)] (D : Λ ⥤ Over S) (X : (Over S)ᵒᵖ ⥤ Type u) : Prop where
  /-- Every stage of the diagram is an affine scheme. -/
  isAffine_obj : ∀ i, AlgebraicGeometry.IsAffine (D.obj i).left
  /-- Every transition of the diagram is a thickening. -/
  isThickening_map : ∀ {i j : Λ} (f : i ⟶ j), IsThickening (D.map f).left
  /-- `X` is a sheaf for the big fppf topology on `Over S`. -/
  isSheaf : Presheaf.IsSheaf (Scheme.fppfTopology.over S) X
  /-- The comparison from the Yoneda presheaf colimit of `D` to `X` is an
  fppf-local isomorphism. -/
  exists_colimit :
    ∃ (c : Cocone (D ⋙ yoneda)) (η : c.pt ⟶ X),
      Nonempty (IsColimit c) ∧
        Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S) η ∧
          Presheaf.IsLocallyInjective (Scheme.fppfTopology.over S) η

namespace IsDirectedAffineThickeningColimit

/-- The constant diagram on an affine scheme over `S` is a directed affine
thickening colimit of the corresponding representable functor. -/
instance instConst {S : Scheme.{u}} (U : Over S)
    [AlgebraicGeometry.IsAffine U.left] :
    IsDirectedAffineThickeningColimit ((Functor.const PUnit.{u + 1}).obj U)
      (yoneda.obj U) :=
  sorry

/-- A directed affine thickening colimit unpacks as affine stages, thickening
transitions, an fppf sheaf, and an fppf-local isomorphism from the Yoneda
presheaf colimit. -/
theorem spec {S : Scheme.{u}} {Λ : Type v} [Preorder Λ] [IsDirected Λ (· ≤ ·)]
    (D : Λ ⥤ Over S) (X : (Over S)ᵒᵖ ⥤ Type u)
    [IsDirectedAffineThickeningColimit D X] :
    (∀ i, AlgebraicGeometry.IsAffine (D.obj i).left) ∧
      (∀ {i j : Λ} (f : i ⟶ j), IsThickening (D.map f).left) ∧
        Presheaf.IsSheaf (Scheme.fppfTopology.over S) X ∧
          ∃ (c : Cocone (D ⋙ yoneda)) (η : c.pt ⟶ X),
            Nonempty (IsColimit c) ∧
              Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S) η ∧
                Presheaf.IsLocallyInjective (Scheme.fppfTopology.over S) η :=
  sorry

end IsDirectedAffineThickeningColimit

/-- A functor of points on schemes over `S` is an affine formal algebraic space
when it is a directed affine thickening colimit and is a coequalizer of two
maps of representable sheaves. -/
class IsAffine {S : Scheme.{u}} (X : (Over S)ᵒᵖ ⥤ Type u) : Prop where
  /-- There is a directed affine thickening presentation of `X`. -/
  exists_colimit :
    ∃ (Λ : Type u) (_ : Preorder Λ) (_ : IsDirected Λ (· ≤ ·)) (D : Λ ⥤ Over S),
      IsDirectedAffineThickeningColimit D X
  /-- There exist schemes `U`, `R` over `S` with fppf-locally surjective maps
  `yoneda.obj U ⟶ X` and `yoneda.obj R ⟶ U ×_X U`. -/
  exists_presentation :
    ∃ (U R : Over S) (πU : yoneda.obj U ⟶ X) (σ : yoneda.obj R ⟶ pullback πU πU),
      Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S) πU ∧
        Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S) σ

namespace IsAffine

/-- Exhibit an affine formal algebraic space by a directed affine thickening
colimit together with a representable coequalizer presentation. -/
theorem of {S : Scheme.{u}} {X : (Over S)ᵒᵖ ⥤ Type u} {Λ : Type u}
    [Preorder Λ] [IsDirected Λ (· ≤ ·)] (D : Λ ⥤ Over S)
    (hcolim : IsDirectedAffineThickeningColimit D X)
    {U R : Over S} (πU : yoneda.obj U ⟶ X) (σ : yoneda.obj R ⟶ pullback πU πU)
    (hπU : Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S) πU)
    (hσ : Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S) σ) :
    IsAffine X :=
  sorry

/-- An affine formal algebraic space unpacks as a directed affine thickening
colimit together with a representable coequalizer presentation. -/
theorem spec {S : Scheme.{u}} (X : (Over S)ᵒᵖ ⥤ Type u) [IsAffine X] :
    (∃ (Λ : Type u) (_ : Preorder Λ) (_ : IsDirected Λ (· ≤ ·)) (D : Λ ⥤ Over S),
      IsDirectedAffineThickeningColimit D X) ∧
      ∃ (U R : Over S) (πU : yoneda.obj U ⟶ X) (σ : yoneda.obj R ⟶ pullback πU πU),
        Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S) πU ∧
          Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S) σ :=
  sorry

/-- Affine formal algebraic spaces are exactly directed affine thickening
colimits satisfying the coequalizer size condition. -/
theorem iff {S : Scheme.{u}} (X : (Over S)ᵒᵖ ⥤ Type u) :
    IsAffine X ↔
      (∃ (Λ : Type u) (_ : Preorder Λ) (_ : IsDirected Λ (· ≤ ·))
          (D : Λ ⥤ Over S),
        IsDirectedAffineThickeningColimit D X) ∧
        ∃ (U R : Over S) (πU : yoneda.obj U ⟶ X)
          (σ : yoneda.obj R ⟶ pullback πU πU),
          Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S) πU ∧
            Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S) σ :=
  sorry

/-- The representable functor of an affine scheme over `S` is an affine formal
algebraic space, via the constant directed system. -/
instance instYoneda {S : Scheme.{u}} (U : Over S)
    [AlgebraicGeometry.IsAffine U.left] :
    IsAffine (yoneda.obj U) :=
  sorry

/-- An affine formal algebraic space is a formal algebraic space. -/
instance instIsFormalAlgebraicSpace {S : Scheme.{u}}
    (X : (Over S)ᵒᵖ ⥤ Type u) [IsAffine X] :
    IsFormalAlgebraicSpace X :=
  sorry

end IsAffine

end AlgebraicGeometry.AffineFormalAlgebraicSpace
