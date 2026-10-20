/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.Basic

/-!
# Affine presentations and countable indexing

Affine formal algebraic spaces admit directed affine thickening presentations
and satisfy the representable coequalizer size condition. Countable indexing
means that such a presentation can be indexed by the natural numbers.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.FormalAlgebraicSpace Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.AffineFormalAlgebraicSpace

/-- A functor of points on schemes over `S` is an affine formal algebraic space
when it is a directed affine thickening colimit and is a coequalizer of two
maps of representable sheaves. -/
class IsAffine {S : Scheme.{u}} (X : (Over S)ᵒᵖ ⥤ Type u) : Prop where
  /-- There is a directed affine thickening presentation of `X`. -/
  exists_colimit :
    ∃ (Λ : Type u) (_ : Preorder Λ) (_ : IsDirected Λ (· ≤ ·)) (D : Λ ⥤ Over S),
      FormalAlgebraicSpace.IsDirectedAffineThickeningColimit D X
  /-- There exist schemes `U`, `R` over `S` with fppf-locally surjective maps
  `yoneda.obj U ⟶ X` and `yoneda.obj R ⟶ U ×_X U`. -/
  exists_presentation :
    ∃ (U R : Over S) (πU : yoneda.obj U ⟶ X) (σ : yoneda.obj R ⟶ pullback πU πU),
      Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S) πU ∧
        Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S) σ

namespace IsAffine

/-- A directed affine thickening colimit with a representable coequalizer
presentation is an affine formal algebraic space. -/
theorem of {S : Scheme.{u}} {X : (Over S)ᵒᵖ ⥤ Type u} {Λ : Type u}
    [Preorder Λ] [IsDirected Λ (· ≤ ·)] (D : Λ ⥤ Over S)
    (hcolim : FormalAlgebraicSpace.IsDirectedAffineThickeningColimit D X)
    {U R : Over S} (πU : yoneda.obj U ⟶ X) (σ : yoneda.obj R ⟶ pullback πU πU)
    (hπU : Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S) πU)
    (hσ : Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S) σ) :
    IsAffine X :=
  sorry

/-- An affine formal algebraic space unpacks as a directed affine thickening
colimit together with a representable coequalizer presentation. -/
theorem spec {S : Scheme.{u}} (X : (Over S)ᵒᵖ ⥤ Type u) [IsAffine X] :
    (∃ (Λ : Type u) (_ : Preorder Λ) (_ : IsDirected Λ (· ≤ ·)) (D : Λ ⥤ Over S),
      FormalAlgebraicSpace.IsDirectedAffineThickeningColimit D X) ∧
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
        FormalAlgebraicSpace.IsDirectedAffineThickeningColimit D X) ∧
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


/-- An affine formal algebraic space is countably indexed when it admits an
`ℕ`-indexed directed affine thickening presentation. -/
class IsCountablyIndexedAffine {S : Scheme.{u}} (X : (Over S)ᵒᵖ ⥤ Type u) : Prop
    extends IsAffine X where
  /-- There is an `ℕ`-indexed directed affine thickening presentation of
  `X`. -/
  exists_nat_colimit :
    ∃ D : ℕ ⥤ Over S, FormalAlgebraicSpace.IsDirectedAffineThickeningColimit D X

namespace IsCountablyIndexedAffine

/-- An affine formal algebraic space admitting an `ℕ`-indexed directed affine
thickening presentation is countably indexed. -/
theorem of {S : Scheme.{u}} {X : (Over S)ᵒᵖ ⥤ Type u} [IsAffine X]
    (D : ℕ ⥤ Over S) (h : FormalAlgebraicSpace.IsDirectedAffineThickeningColimit D X) :
    IsCountablyIndexedAffine X :=
  sorry

/-- A countably indexed affine formal algebraic space unpacks as an affine
formal algebraic space together with an `ℕ`-indexed directed affine thickening
presentation. -/
theorem spec {S : Scheme.{u}} (X : (Over S)ᵒᵖ ⥤ Type u)
    [IsCountablyIndexedAffine X] :
    IsAffine X ∧ ∃ D : ℕ ⥤ Over S, FormalAlgebraicSpace.IsDirectedAffineThickeningColimit D X :=
  sorry

/-- An affine formal algebraic space is countably indexed if and only if it
admits an `ℕ`-indexed directed affine thickening presentation. -/
theorem iff {S : Scheme.{u}} (X : (Over S)ᵒᵖ ⥤ Type u) :
    IsCountablyIndexedAffine X ↔
      IsAffine X ∧ ∃ D : ℕ ⥤ Over S, FormalAlgebraicSpace.IsDirectedAffineThickeningColimit D X :=
  sorry

/-- The representable functor of an affine scheme over `S` is countably
indexed, via the constant sequential system. -/
instance instYoneda {S : Scheme.{u}} (U : Over S)
    [AlgebraicGeometry.IsAffine U.left] :
    IsCountablyIndexedAffine (yoneda.obj U) :=
  sorry

end IsCountablyIndexedAffine


end AlgebraicGeometry.AffineFormalAlgebraicSpace
