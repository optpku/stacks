module

public import Mathlib.Topology.LocallyFinsupp
public import stacks_project.Chap65.Definition_65_13_2_Separation
public import stacks_project.Chap67.Definition_67_4_2_Separation
public import stacks_project.Chap67.Definition_67_33_2_RelativeDimension
public import stacks_project.Chap67.Lemma_67_30_5_Flat
public import stacks_project.Chap69.Lemma_69_12_2_Coherent
public import stacks_project.Chap69.Lemma_69_12_7_Coherent
public import stacks_project.Chap76.Lemma_76_32_2
import stacks_project.Chap82.Lemma_82_10_4_Pullback

/-!
# Flat pullback for associated-cycle identities

The cycle operation is the existing flat pullback of Lemma 82.10.4. Its
implementation import stays private so that the target can use the canonical
dimension and module-cycle owners without re-exporting duplicate dimension names.
-/

public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace Modules

/-- Pullback of a coherent `𝒪_Y`-module along a morphism of locally Noetherian
algebraic spaces is coherent. -/
instance instIsCoherent_pullback {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y] (f : X ⟶ Y)
    (F : Y.Modules) [F.IsCoherent] :
    ((pullback f).obj F).IsCoherent := sorry

end Modules

namespace Hom

/-- The canonical flat pullback of Lemma 82.10.4, exposed without its
conflicting dimension exports. -/
noncomputable def flatPullbackCycle {S : Scheme.{u}} {B X Y : AlgebraicSpace S}
    [UniversallyCatenary B] [IsQuasiSeparated B]
    (pY : Y ⟶ B) [QuasiSeparated pY] [LocallyOfFiniteType pY]
    (pX : X ⟶ B) [QuasiSeparated pX] [LocallyOfFiniteType pX]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (f : X ⟶ Y) (r : ℕ) [Flat f] [RelativeDimension f r]
    (hf : f ≫ pY = pX) (k : ℤ) (α : Function.locallyFinsupp (Points Y) ℤ) :
    Function.locallyFinsupp (Points X) ℤ :=
  flatPullback pY pX δ f r hf k α

/-- Canonical flat pullback sends the zero cycle to zero. -/
theorem flatPullbackCycle_zero {S : Scheme.{u}} {B X Y : AlgebraicSpace S}
    [UniversallyCatenary B] [IsQuasiSeparated B]
    (pY : Y ⟶ B) [QuasiSeparated pY] [LocallyOfFiniteType pY]
    (pX : X ⟶ B) [QuasiSeparated pX] [LocallyOfFiniteType pX]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (f : X ⟶ Y) (r : ℕ) [Flat f] [RelativeDimension f r]
    (hf : f ≫ pY = pX) (k : ℤ) :
    flatPullbackCycle pY pX δ f r hf k 0 = 0 := sorry

/-- Canonical flat pullback preserves addition of cycles. -/
theorem flatPullbackCycle_add {S : Scheme.{u}} {B X Y : AlgebraicSpace S}
    [UniversallyCatenary B] [IsQuasiSeparated B]
    (pY : Y ⟶ B) [QuasiSeparated pY] [LocallyOfFiniteType pY]
    (pX : X ⟶ B) [QuasiSeparated pX] [LocallyOfFiniteType pX]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (f : X ⟶ Y) (r : ℕ) [Flat f] [RelativeDimension f r]
    (hf : f ≫ pY = pX) (k : ℤ)
    (α β : Function.locallyFinsupp (Points Y) ℤ) :
    flatPullbackCycle pY pX δ f r hf k (α + β) =
      flatPullbackCycle pY pX δ f r hf k α +
        flatPullbackCycle pY pX δ f r hf k β := sorry

end Hom

end AlgebraicGeometry.AlgebraicSpace
