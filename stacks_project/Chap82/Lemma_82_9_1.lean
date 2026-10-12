/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap67.Definition_67_18_1_Dominant
public import stacks_project.Chap67.Definition_67_33_2_RelativeDimension
public import stacks_project.Chap67.Lemma_67_30_5_Flat
public import stacks_project.Chap72.Lemma_72_4_7_IntegralClosed
public import stacks_project.Chap82.Definition_82_2_5_DeltaDimension

/-!
# δ-dimension of inverse images under flat morphisms of relative dimension `r`

In the good setup of Situation 82.2.1, a flat morphism of relative dimension `r`
shifts `δ`-dimension of nonempty closed inverse images, and of irreducible
components of inverse images of integral closed subspaces, by `r`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace TopologicalSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Hom

/-- Lemma 82.9.1 (1): In Situation 82.2.1 let `X, Y / B` be good. Let `f : X ⟶ Y`
be a morphism over `B`. If `f` is flat of relative dimension `r`, then for any
closed subset `T ⊂ |Y|` with nonempty `|f|⁻¹(T)`,
`pX.closedSetDeltaDimension δ (T.preimage (Points.continuous_map f)) =
pY.closedSetDeltaDimension δ T + (r : EInt)`. -/
@[stacks 0EP5]
theorem closedPreimageDeltaDimension {S : Scheme.{u}}
    {B X Y : AlgebraicSpace S} [UniversallyCatenary B] [IsQuasiSeparated B]
    (pY : Y ⟶ B) [QuasiSeparated pY] [LocallyOfFiniteType pY]
    (pX : X ⟶ B) [QuasiSeparated pX] [LocallyOfFiniteType pX]
    (δ : Points B → ℤ) [IsDimensionFunction δ] (f : X ⟶ Y) (r : ℕ)
    [Flat f] [RelativeDimension f r] (hf : f ≫ pY = pX)
    (T : Closeds (Points Y)) (hT : Nonempty (T.preimage (Points.continuous_map f))) :
    pX.closedSetDeltaDimension δ (T.preimage (Points.continuous_map f)) =
      pY.closedSetDeltaDimension δ T + (r : EInt) :=
  sorry

/-- Lemma 82.9.1 (2): In Situation 82.2.1 let `X, Y / B` be good. Let `f : X ⟶ Y`
be a morphism over `B`. If `f` is flat of relative dimension `r`, `Z ⊂ |Y|` is
irreducible closed, and `Z'` is an irreducible component of `|f|⁻¹(Z)`, then
`Z'` dominates `Z`, i.e.
`IrreducibleCloseds.map (Points.map f) (Points.continuous_map f) Z' = Z`. -/
@[stacks 0EP5]
theorem componentOfPreimageMapsTo {S : Scheme.{u}}
    {B X Y : AlgebraicSpace S} [UniversallyCatenary B] [IsQuasiSeparated B]
    (pY : Y ⟶ B) [QuasiSeparated pY] [LocallyOfFiniteType pY]
    (pX : X ⟶ B) [QuasiSeparated pX] [LocallyOfFiniteType pX]
    (δ : Points B → ℤ) [IsDimensionFunction δ] (f : X ⟶ Y) (r : ℕ)
    [Flat f] [RelativeDimension f r] (hf : f ≫ pY = pX)
    (Z : IrreducibleCloseds (Points Y)) (Z' : IrreducibleCloseds (Points X))
    (hZ' : Z' ∈ closedSetIrreducibleComponents
      (Closeds.preimage ⟨Z.carrier, Z.isClosed⟩ (Points.continuous_map f))) :
    IrreducibleCloseds.map (Points.map f) (Points.continuous_map f) Z' = Z :=
  sorry

/-- Lemma 82.9.1 (3): In Situation 82.2.1 let `X, Y / B` be good. Let `f : X ⟶ Y`
be a morphism over `B`. If `f` is flat of relative dimension `r`, `Z ⊂ |Y|` is
irreducible closed, and `Z'` is an irreducible component of `|f|⁻¹(Z)`, then
`pX.deltaDimension δ Z' = pY.deltaDimension δ Z + (r : ℤ)`. -/
@[stacks 0EP5]
theorem componentOfPreimageDeltaDimension {S : Scheme.{u}}
    {B X Y : AlgebraicSpace S} [UniversallyCatenary B] [IsQuasiSeparated B]
    (pY : Y ⟶ B) [QuasiSeparated pY] [LocallyOfFiniteType pY]
    (pX : X ⟶ B) [QuasiSeparated pX] [LocallyOfFiniteType pX]
    (δ : Points B → ℤ) [IsDimensionFunction δ] (f : X ⟶ Y) (r : ℕ)
    [Flat f] [RelativeDimension f r] (hf : f ≫ pY = pX)
    (Z : IrreducibleCloseds (Points Y)) (Z' : IrreducibleCloseds (Points X))
    (hZ' : Z' ∈ closedSetIrreducibleComponents
      (Closeds.preimage ⟨Z.carrier, Z.isClosed⟩ (Points.continuous_map f))) :
    pX.deltaDimension δ Z' = pY.deltaDimension δ Z + (r : ℤ) :=
  sorry

/-- If `Z ⊂ Y` is an integral closed subspace and `Z' ⊂ X` is an integral closed
subspace whose point-set is an irreducible component of `|f|⁻¹(|Z|)`, then there
is a dominant morphism `g : Z'.X ⟶ Z.X` over `f`. -/
theorem componentOfInverseImage_dominant {S : Scheme.{u}}
    {B X Y : AlgebraicSpace S} [UniversallyCatenary B] [IsQuasiSeparated B]
    (pY : Y ⟶ B) [QuasiSeparated pY] [LocallyOfFiniteType pY]
    (pX : X ⟶ B) [QuasiSeparated pX] [LocallyOfFiniteType pX]
    (δ : Points B → ℤ) [IsDimensionFunction δ] (f : X ⟶ Y) (r : ℕ)
    [Flat f] [RelativeDimension f r] (hf : f ≫ pY = pX)
    (Z : ClosedSubspace Y) [IsIntegral Z.X] (Z' : ClosedSubspace X)
    [IsIntegral Z'.X]
    (hZ' : ClosedSubspace.irreducibleClosed Z' ∈
      closedSetIrreducibleComponents
        (Closeds.preimage ⟨Z.pointsSet, Z.isClosed_pointsSet⟩
          (Points.continuous_map f))) :
    ∃ g : Z'.X ⟶ Z.X, g ≫ Z.ι = Z'.ι ≫ f ∧ Dominant g :=
  sorry

/-- If `Z ⊂ Y` is an integral closed subspace and `Z' ⊂ X` is an integral closed
subspace whose point-set is an irreducible component of `|f|⁻¹(|Z|)`, then
`pX.deltaDimension δ (ClosedSubspace.irreducibleClosed Z') =
pY.deltaDimension δ (ClosedSubspace.irreducibleClosed Z) + (r : ℤ)`. -/
theorem componentOfInverseImage_deltaDimension {S : Scheme.{u}}
    {B X Y : AlgebraicSpace S} [UniversallyCatenary B] [IsQuasiSeparated B]
    (pY : Y ⟶ B) [QuasiSeparated pY] [LocallyOfFiniteType pY]
    (pX : X ⟶ B) [QuasiSeparated pX] [LocallyOfFiniteType pX]
    (δ : Points B → ℤ) [IsDimensionFunction δ] (f : X ⟶ Y) (r : ℕ)
    [Flat f] [RelativeDimension f r] (hf : f ≫ pY = pX)
    (Z : ClosedSubspace Y) [IsIntegral Z.X] (Z' : ClosedSubspace X)
    [IsIntegral Z'.X]
    (hZ' : ClosedSubspace.irreducibleClosed Z' ∈
      closedSetIrreducibleComponents
        (Closeds.preimage ⟨Z.pointsSet, Z.isClosed_pointsSet⟩
          (Points.continuous_map f))) :
    pX.deltaDimension δ (ClosedSubspace.irreducibleClosed Z') =
      pY.deltaDimension δ (ClosedSubspace.irreducibleClosed Z) + (r : ℤ) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Hom
