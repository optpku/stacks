module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.InvertiblePullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Point.ClosureIntegral

public import Mathlib.Topology.LocallyFinsupp
public import ReasLib.CategoryTheory.Monoidal.Invertible
public import stacks_project.Chap65.Definition_65_13_2_Separation
public import stacks_project.Chap67.Definition_67_4_2_Separation
public import stacks_project.Chap67.Definition_67_33_2_RelativeDimension
public import stacks_project.Chap67.Lemma_67_23_5
public import stacks_project.Chap67.Lemma_67_30_5_Flat
public import stacks_project.Chap68.Definition_68_25_4_UniversallyCatenary
public import stacks_project.Chap69.Lemma_69_12_5_Monoidal
public import stacks_project.Chap69.Lemma_69_12_7_Coherent
public import stacks_project.Chap69.Lemma_69_17_2_Pullback
public import stacks_project.Chap72.Definition_72_4_1_Integral
public import stacks_project.Chap76.Lemma_76_32_2
public import stacks_project.Chap82.Definition_82_3_1_CycleGroup
public import stacks_project.Chap82.Remark_82_5_1_IrreducibleComponent
import stacks_project.Chap82.Lemma_82_16_1

/-!
# Import-isolated flat components and cycle pullback

`Hom.flatPullback`, `Hom.flatComponent`, and
`ClosedSubspace.componentMultiplicity` cannot be co-imported with
meromorphic-section files, because those chains collide on
`GeometricPoint.toSmallEtalePoint_fiber_obj`. This module privately imports
Lemma 82.16.1 and re-exports those names as public wrappers.
-/

public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.MonoidalCategory
open Function

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Flat pullback of a cycle along a morphism of relative dimension `r`. -/
noncomputable def flatPullback {S : Scheme.{u}} {B X Y : AlgebraicSpace S}
    [UniversallyCatenary B] [IsQuasiSeparated B]
    (pY : Y ⟶ B) [QuasiSeparated pY] [LocallyOfFiniteType pY]
    (pX : X ⟶ B) [QuasiSeparated pX] [LocallyOfFiniteType pX]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (f : X ⟶ Y) (r : ℕ) [Flat f] [RelativeDimension f r]
    (hf : f ≫ pY = pX) (k : ℤ) (α : Function.locallyFinsupp (Points Y) ℤ) :
    Function.locallyFinsupp (Points X) ℤ :=
  Hom.flatPullback pY pX δ f r hf k α

/-- The canonical irreducible component of `X` on a generic point. -/
@[expose] noncomputable def flatComponent {S : Scheme.{u}} {B X : AlgebraicSpace S}
    [IsQuasiSeparated B] (pX : X ⟶ B) [QuasiSeparated pX]
    (η : genericPoints X) : ClosedSubspace X :=
  let _ := pX
  ClosedSubspace.ofι (PointClosure.ι η.1)

/-- The canonical irreducible component on a generic point is integral. -/
theorem isIntegral_flatComponent {S : Scheme.{u}} {B X : AlgebraicSpace S}
    [IsQuasiSeparated B] (pX : X ⟶ B) [QuasiSeparated pX]
    (η : genericPoints X) : IsIntegral (flatComponent pX η).X :=
  Hom.isIntegral_flatComponent pX η

/-- The multiplicity of an irreducible component of a closed subspace. -/
noncomputable def componentMultiplicity {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsLocallyNoetherian X] (Y : ClosedSubspace X) (η : genericPoints Y.X) : ℕ :=
  ClosedSubspace.componentMultiplicity Y η

end AlgebraicGeometry.AlgebraicSpace
