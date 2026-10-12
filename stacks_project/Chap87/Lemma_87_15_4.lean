/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import stacks_project.Chap87.Lemma_87_12_1

/-!
# Reduction of fibre products of formal algebraic spaces

The reduction of a fibre product of formal algebraic spaces is isomorphic to
the reduction of the fibre product of the reductions.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.GrothendieckTopology
open AlgebraicGeometry.ChosenBigFppfSite
open AlgebraicGeometry.IsFormalAlgebraicSpace

noncomputable section

universe u v

namespace AlgebraicGeometry.IsFormalAlgebraicSpace

/-- The comparison morphism `pullback φ ψ ⟶ pullback f g` induced by the
reduction inclusions of `X`, `Y`, and `Z`. -/
def reductionPullbackComparison {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    {X Y Z : Sheaf (𝒮.bigTopology S) (Type (max u v))}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]
    [IsFormalAlgebraicSpace Z] (f : X ⟶ Z) (g : Y ⟶ Z)
    {φ : reduction X ⟶ reduction Z} {ψ : reduction Y ⟶ reduction Z}
    (hφ : φ ≫ reductionι Z = reductionι X ≫ f)
    (hψ : ψ ≫ reductionι Z = reductionι Y ≫ g) :
    pullback φ ψ ⟶ pullback f g :=
  pullback.map φ ψ f g (reductionι X) (reductionι Y) (reductionι Z) hφ hψ

/-- The comparison morphism commutes with first projections. -/
theorem reductionPullbackComparison_fst {𝒮 : ChosenBigFppfSite.{u, v}}
    {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    {X Y Z : Sheaf (𝒮.bigTopology S) (Type (max u v))}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]
    [IsFormalAlgebraicSpace Z] (f : X ⟶ Z) (g : Y ⟶ Z)
    {φ : reduction X ⟶ reduction Z} {ψ : reduction Y ⟶ reduction Z}
    (hφ : φ ≫ reductionι Z = reductionι X ≫ f)
    (hψ : ψ ≫ reductionι Z = reductionι Y ≫ g) :
    reductionPullbackComparison f g hφ hψ ≫ pullback.fst f g =
      pullback.fst φ ψ ≫ reductionι X :=
  sorry

/-- The comparison morphism commutes with second projections. -/
theorem reductionPullbackComparison_snd {𝒮 : ChosenBigFppfSite.{u, v}}
    {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    {X Y Z : Sheaf (𝒮.bigTopology S) (Type (max u v))}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]
    [IsFormalAlgebraicSpace Z] (f : X ⟶ Z) (g : Y ⟶ Z)
    {φ : reduction X ⟶ reduction Z} {ψ : reduction Y ⟶ reduction Z}
    (hφ : φ ≫ reductionι Z = reductionι X ≫ f)
    (hψ : ψ ≫ reductionι Z = reductionι Y ≫ g) :
    reductionPullbackComparison f g hφ hψ ≫ pullback.snd f g =
      pullback.snd φ ψ ≫ reductionι Y :=
  sorry

/-- Lemma 87.15.4: Let `S` be a scheme. Let `f : X ⟶ Z` and `g : Y ⟶ Z` be
morphisms of formal algebraic spaces over `S`. Then
`(X ×_Z Y)_red ≅ (X_red ×_{Z_red} Y_red)_red`: any morphism
`e : reduction (pullback φ ψ) ⟶ reduction (pullback f g)` over the comparison
`X_red ×_{Z_red} Y_red ⟶ X ×_Z Y` is an isomorphism. -/
@[stacks 0CB9]
theorem reduction_pullback {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    {X Y Z : Sheaf (𝒮.bigTopology S) (Type (max u v))}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]
    [IsFormalAlgebraicSpace Z] (f : X ⟶ Z) (g : Y ⟶ Z)
    [IsFormalAlgebraicSpace (pullback f g)]
    {φ : reduction X ⟶ reduction Z} {ψ : reduction Y ⟶ reduction Z}
    (hφ : φ ≫ reductionι Z = reductionι X ≫ f)
    (hψ : ψ ≫ reductionι Z = reductionι Y ≫ g)
    [IsFormalAlgebraicSpace (pullback φ ψ)]
    {e : reduction (pullback φ ψ) ⟶ reduction (pullback f g)}
    (he : e ≫ reductionι (pullback f g) =
      reductionι (pullback φ ψ) ≫ reductionPullbackComparison f g hφ hψ) :
    IsIso e :=
  sorry

end AlgebraicGeometry.IsFormalAlgebraicSpace

