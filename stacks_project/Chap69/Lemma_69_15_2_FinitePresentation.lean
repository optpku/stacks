module

public import Mathlib.CategoryTheory.ObjectProperty.Ind
public import stacks_project.Chap66.Definition_66_24_1_Noetherian
public import stacks_project.Chap66.Definition_66_29_1_RingedSite
public import stacks_project.Chap67.Definition_67_20_2_Affine

/-!
# Filtered colimits of finitely presented modules

If `f : X ⟶ Y` is an affine morphism of algebraic spaces and `Y` is Noetherian, every
quasi-coherent `𝒪_X`-module is a small filtered colimit of finitely presented modules.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

/-- If `f : X ⟶ Y` is an affine morphism of algebraic spaces over a scheme `S` and `Y` is
Noetherian, then every quasi-coherent `𝒪_X`-module is a small filtered colimit of finitely
presented `𝒪_X`-modules. -/
theorem isFinitePresentation_ind {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [Affine f] [IsNoetherian Y] (F : X.Modules) [F.IsQuasicoherent] :
    (SheafOfModules.isFinitePresentation (structureSheaf X)).ind.{u} F :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules
