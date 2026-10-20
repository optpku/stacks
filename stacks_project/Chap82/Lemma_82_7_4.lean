/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Dimension.GenericallyFinite
import StacksCheckRecall

/-!
# Equal δ-dimension morphisms of good integral algebraic spaces

In Situation 82.2.1, a morphism of good integral algebraic spaces of equal
`δ`-dimension over `B` either factors through a proper closed subspace of the
target or is dominant with finite function-field extension.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Hom

universe u

/- Lemma 82.7.4: In Situation 82.2.1, a morphism over `B` between good integral
algebraic spaces with equal `δ`-dimensions either factors through a proper closed
subspace of the target or is dominant with finite function-field extension.
The dimensions are evaluated at generic points, whose residue fields are the
function fields; a proper closed subspace has point-set different from `Set.univ`. -/
@[stacks 0ENY] #check (AlgebraicGeometry.AlgebraicSpace.Hom.factorsThrough_properClosed_or_finiteResidueFieldExtension :
    ∀ {S : Scheme.{u}} {B X Y : AlgebraicSpace S}
    [UniversallyCatenary B] [IsQuasiSeparated B]
    (pX : X ⟶ B) (pY : Y ⟶ B)
    [QuasiSeparated pX] [LocallyOfFiniteType pX]
    [QuasiSeparated pY] [LocallyOfFiniteType pY]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ Y) (hf : f ≫ pY = pX)
    {x : Points X} {y : Points Y}
    (hx : x ∈ genericPoints X) (hy : y ∈ genericPoints Y)
    (hdim : AlgebraicGeometry.AlgebraicSpace.Hom.relativeDimensionFunction pX δ x = AlgebraicGeometry.AlgebraicSpace.Hom.relativeDimensionFunction pY δ y),
    (∃ Z : ClosedSubspace Y,
        Z.pointsSet ≠ Set.univ ∧ ∃ g : X ⟶ Z.X, g ≫ Z.ι = f) ∨
      (Dominant f ∧ FiniteResidueFieldExtensionAt f x))

-- The dominant case has finite generic residue-field extension.
#check (AlgebraicGeometry.AlgebraicSpace.Hom.finiteResidueFieldExtension_of_eq_deltaDimension :
    ∀ {S : Scheme.{u}} {B X Y : AlgebraicSpace S}
    [UniversallyCatenary B] [IsQuasiSeparated B]
    (pX : X ⟶ B) (pY : Y ⟶ B)
    [QuasiSeparated pX] [LocallyOfFiniteType pX]
    [QuasiSeparated pY] [LocallyOfFiniteType pY]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ Y) (hf : f ≫ pY = pX) [Dominant f]
    {x : Points X} {y : Points Y}
    (hx : x ∈ genericPoints X) (hy : y ∈ genericPoints Y)
    (hdim : AlgebraicGeometry.AlgebraicSpace.Hom.relativeDimensionFunction pX δ x = AlgebraicGeometry.AlgebraicSpace.Hom.relativeDimensionFunction pY δ y),
    FiniteResidueFieldExtension f)
