module

public import Mathlib.CategoryTheory.CommSq
public import stacks_project.Chap67.Definition_67_13_2_InverseImage
public import stacks_project.Chap67.Lemma_67_13_5_Complement
public import stacks_project.Chap67.Lemma_67_28_8_FinitePresentation
public import stacks_project.Chap67.Lemma_67_30_5_Flat

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FormalGlueing

/-! # Formal glueing and restriction to open complements -/

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

#check (AlgebraicGeometry.AlgebraicSpace.IsFormalGlueing :
  ∀ {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} (f : Y ⟶ X) (i : Z ⟶ X),
    [QuasiCompact f] → [QuasiSeparated f] → [IsClosedImmersion i] →
    [FinitePresentation i] → Prop)

#check (AlgebraicGeometry.AlgebraicSpace.restrictToComplement :
  ∀ {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} (f : Y ⟶ X) (i : Z ⟶ X),
    [IsClosedImmersion i] →
    closedImmersionComplement (inverseImageι f i) ⟶ closedImmersionComplement i)
