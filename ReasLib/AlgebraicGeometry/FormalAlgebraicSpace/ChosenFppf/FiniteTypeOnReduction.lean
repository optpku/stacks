/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.ChosenFppf.LocalMorphismProperty
public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.ChosenFppf.Reduction
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ChosenFppf.FiniteType
public import ReasLib.RingTheory.Topology.FiniteType.Reduction

/-!
# Finite type on reductions of formal algebraic spaces

Local finite type of the induced reduction morphism is characterized by finite
type on reduction on affine étale charts and covers.
-/

@[expose] public section

universe u v

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.ChosenBigFppfSite IsFormalAlgebraicSpace TopologicalRing RingHom

namespace AlgebraicGeometry.IsLocallyCountablyIndexed

variable {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
variable [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
variable [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
variable {X Y : Sheaf (𝒮.bigTopology S) (Type (max u v))}
variable [IsLocallyCountablyIndexed X] [IsLocallyCountablyIndexed Y]

/-- The morphism `f : X ⟶ Y` of locally countably indexed formal algebraic
spaces has reduction locally of finite type when every sheaf map
`φ : reduction X ⟶ reduction Y` satisfying
`φ ≫ reductionι Y = reductionι X ≫ f` is locally of finite type on étale
squares. -/
def locallyOfFiniteTypeOnReduction (f : X ⟶ Y) : Prop :=
  ∀ φ : reduction X ⟶ reduction Y,
    φ ≫ reductionι Y = reductionι X ≫ f → locallyOfFiniteTypeOnEtaleSquares φ

/-- Finite type on reduction of a morphism is equivalent to existence of a
compatible map of reductions that is locally of finite type on étale squares. -/
theorem locallyOfFiniteTypeOnReduction_iff (f : X ⟶ Y)
    [Fact (ChosenBigSite.IsSizeClosed 𝒮)] :
    locallyOfFiniteTypeOnReduction f ↔
      ∃ φ : reduction X ⟶ reduction Y,
        φ ≫ reductionι Y = reductionι X ≫ f ∧
          locallyOfFiniteTypeOnEtaleSquares φ :=
  sorry

/-- For a morphism of locally countably indexed formal algebraic spaces,
finite type on reduction on every affine étale square, on a target cover and
covers of its pullbacks, or on a source cover factoring through affine étale
target charts is equivalent to local finite type of its reduction morphism. -/
theorem locallyOfFiniteTypeOnReduction_tfae (f : X ⟶ Y)
    [Fact (ChosenBigSite.IsSizeClosed 𝒮)] :
    List.TFAE
      [etaleAffineLocally (fun φ ↦ φ.IsFiniteTypeOnReduction) f,
        existsCoverOnTarget (fun φ ↦ φ.IsFiniteTypeOnReduction) f,
        existsCoverOnSource (fun φ ↦ φ.IsFiniteTypeOnReduction) f,
        locallyOfFiniteTypeOnReduction f] :=
  sorry

/-- Testing finite type on reduction on every affine étale square is equivalent
to local finite type of the induced reduction morphism. -/
theorem etaleAffineLocally_iff_locallyOfFiniteTypeOnReduction (f : X ⟶ Y)
    [Fact (ChosenBigSite.IsSizeClosed 𝒮)] :
    etaleAffineLocally (fun φ ↦ φ.IsFiniteTypeOnReduction) f ↔
      locallyOfFiniteTypeOnReduction f :=
  (locallyOfFiniteTypeOnReduction_tfae f).out 0 3

/-- Local finite type of the reduction morphism is equivalent to admitting an
affine étale target cover and affine étale covers of its pullbacks whose maps
to the target charts correspond to ring homomorphisms of finite type on reduction. -/
theorem existsCoverOnTarget_iff_locallyOfFiniteTypeOnReduction (f : X ⟶ Y)
    [Fact (ChosenBigSite.IsSizeClosed 𝒮)] :
    existsCoverOnTarget (fun φ ↦ φ.IsFiniteTypeOnReduction) f ↔
      locallyOfFiniteTypeOnReduction f :=
  (locallyOfFiniteTypeOnReduction_tfae f).out 1 3

/-- Local finite type of the reduction morphism is equivalent to admitting an
affine étale source cover factoring through affine étale target charts by maps
corresponding to ring homomorphisms of finite type on reduction. -/
theorem existsCoverOnSource_iff_locallyOfFiniteTypeOnReduction (f : X ⟶ Y)
    [Fact (ChosenBigSite.IsSizeClosed 𝒮)] :
    existsCoverOnSource (fun φ ↦ φ.IsFiniteTypeOnReduction) f ↔
      locallyOfFiniteTypeOnReduction f :=
  (locallyOfFiniteTypeOnReduction_tfae f).out 2 3

end AlgebraicGeometry.IsLocallyCountablyIndexed
