/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.ChosenFppf.Reduction.Map
public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.ChosenFppf.Limits
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Fppf.Full.Size

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.GrothendieckTopology
open AlgebraicGeometry.ChosenBigFppfSite

noncomputable section

universe u v

namespace AlgebraicGeometry.IsFormalAlgebraicSpace

section ChosenSite

variable {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
  [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
  [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
  {X Y Z : Sheaf (𝒮.bigTopology S) (Type (max u v))}
  [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y] [IsFormalAlgebraicSpace Z]

/-- The reduction inclusions induce a canonical morphism from the pullback
of the reductions to the original pullback. -/
def reductionPullbackComparison (h_size : ChosenBigSite.IsSizeClosed 𝒮)
    (f : X ⟶ Z) (g : Y ⟶ Z) :
    pullback (mapReduction h_size f) (mapReduction h_size g) ⟶ pullback f g :=
  pullback.map (mapReduction h_size f) (mapReduction h_size g) f g
    (reductionι X) (reductionι Y) (reductionι Z)
    (mapReduction_spec h_size f).1 (mapReduction_spec h_size g).1

/-- The canonical pullback comparison commutes with first projections. -/
theorem reductionPullbackComparison_fst (h_size : ChosenBigSite.IsSizeClosed 𝒮)
    (f : X ⟶ Z) (g : Y ⟶ Z) :
    reductionPullbackComparison h_size f g ≫ pullback.fst f g =
      pullback.fst (mapReduction h_size f) (mapReduction h_size g) ≫ reductionι X := sorry

/-- The canonical pullback comparison commutes with second projections. -/
theorem reductionPullbackComparison_snd (h_size : ChosenBigSite.IsSizeClosed 𝒮)
    (f : X ⟶ Z) (g : Y ⟶ Z) :
    reductionPullbackComparison h_size f g ≫ pullback.snd f g =
      pullback.snd (mapReduction h_size f) (mapReduction h_size g) ≫ reductionι Y := sorry

end ChosenSite

section FullSite

variable {S : Scheme.{u}}
  [HasWeakSheafify (full.bigTopology S) (Type (u + 1))]
  [HasPullbacks (Sheaf (full.bigTopology S) (Type (u + 1)))]
  {X Y Z : Sheaf (full.bigTopology S) (Type (u + 1))}
  [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y] [IsFormalAlgebraicSpace Z]

/-- The reduction of the fibre product of the reductions of a cospan of
formal algebraic spaces on the full big fppf site. -/
def reducedPullbackOfReductions (f : X ⟶ Z) (g : Y ⟶ Z) :
    Sheaf (full.bigTopology S) (Type (u + 1)) :=
  let hX := isFormalAlgebraicSpace_reduction isSizeClosed_full X
  let hY := isFormalAlgebraicSpace_reduction isSizeClosed_full Y
  let hZ := isFormalAlgebraicSpace_reduction isSizeClosed_full Z
  @reduction full S _ _
    (pullback (mapReduction isSizeClosed_full f) (mapReduction isSizeClosed_full g))
    (@instIsFormalAlgebraicSpace_pullback S _ _ (reduction X) (reduction Y) (reduction Z)
      hX hY hZ (mapReduction isSizeClosed_full f) (mapReduction isSizeClosed_full g))

/-- The reduction inclusions induce a canonical map from the reduced fibre
product of the reductions to the reduction of the original fibre product. -/
def reductionPullbackMap (f : X ⟶ Z) (g : Y ⟶ Z) :
    reducedPullbackOfReductions f g ⟶ reduction (pullback f g) :=
  let hX := isFormalAlgebraicSpace_reduction isSizeClosed_full X
  let hY := isFormalAlgebraicSpace_reduction isSizeClosed_full Y
  let hZ := isFormalAlgebraicSpace_reduction isSizeClosed_full Z
  @mapReduction full S _ _ isSizeClosed_full
    (pullback (mapReduction isSizeClosed_full f) (mapReduction isSizeClosed_full g))
    (pullback f g)
    (@instIsFormalAlgebraicSpace_pullback S _ _ (reduction X) (reduction Y) (reduction Z)
      hX hY hZ (mapReduction isSizeClosed_full f) (mapReduction isSizeClosed_full g))
    (instIsFormalAlgebraicSpace_pullback f g)
    (reductionPullbackComparison isSizeClosed_full f g)

/-- The canonical comparison from the pullback of reductions of formal
algebraic spaces induces an isomorphism on reductions. -/
instance reductionPullback_isIso (f : X ⟶ Z) (g : Y ⟶ Z) :
    IsIso (reductionPullbackMap f g) := sorry

end FullSite

end AlgebraicGeometry.IsFormalAlgebraicSpace
