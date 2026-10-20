module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FinitePart.Sheaf
public import ReasLib.CategoryTheory.Presheaf.Basic
public import stacks_project.Chap67.Remark_67_12_5_Opens

/-! # Finite-part sections as an unshrunk fppf sheaf -/

open CategoryTheory AlgebraicGeometry AlgebraicSpace Opposite

universe u

#check (AlgebraicGeometry.AlgebraicSpace.finitePartSheaf :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y),
    Sheaf (Scheme.fppfTopology.over S) (Type (u + 1)))

#check (AlgebraicGeometry.AlgebraicSpace.finitePartSheaf_obj :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) (T : Over S),
    (finitePartSheaf f).obj.obj (op T) = FinitePart.Point f T)
