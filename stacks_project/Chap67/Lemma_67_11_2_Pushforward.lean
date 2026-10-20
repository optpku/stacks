module

public import ReasLib.CategoryTheory.ObjectProperty.FullSubcategory.Restriction
public import stacks_project.Chap66.«66_26_0_1_Pushforward»
public import stacks_project.Chap66.Definition_66_29_1_QCoh
public import stacks_project.Chap67.Definition_67_4_2_Separation
public import stacks_project.Chap67.Definition_67_8_2_QuasiCompact

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Quasicoherent.Pushforward

@[expose] public section

open CategoryTheory

universe u

#check (AlgebraicGeometry.AlgebraicSpace.Modules.pushforward.isQuasicoherent :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} {X Y : AlgebraicGeometry.AlgebraicSpace S}
    (f : X ⟶ Y) [AlgebraicGeometry.AlgebraicSpace.QuasiCompact f]
    [AlgebraicGeometry.AlgebraicSpace.QuasiSeparated f]
    (F : AlgebraicGeometry.AlgebraicSpace.Modules X) [F.IsQuasicoherent],
    ((AlgebraicGeometry.AlgebraicSpace.Modules.pushforward f).obj F).IsQuasicoherent)

#check (AlgebraicGeometry.AlgebraicSpace.QCoh.pushforward :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} {X Y : AlgebraicGeometry.AlgebraicSpace S}
    (f : X ⟶ Y) [AlgebraicGeometry.AlgebraicSpace.QuasiCompact f]
    [AlgebraicGeometry.AlgebraicSpace.QuasiSeparated f],
    AlgebraicGeometry.AlgebraicSpace.QCoh X ⥤ AlgebraicGeometry.AlgebraicSpace.QCoh Y)
