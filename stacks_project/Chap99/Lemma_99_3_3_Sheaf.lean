module

public import Mathlib.CategoryTheory.Sites.Sheaf
public import Mathlib.CategoryTheory.Yoneda
public import stacks_project.Chap97.Lemma_97_11_4_RelativeHom
public import stacks_project.Chap99.Lemma_99_3_3_SpaceHom

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.HomSheaf

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

/- The Hom sheaf comparison sends a pair over an algebraic space to its canonical
morphism of fppf sheaves. -/
#check (AlgebraicGeometry.AlgebraicSpace.Modules.toSheafHom :
  ∀ {S : Scheme.{u}} {X B : AlgebraicSpace S} (f : X ⟶ B) (F G : X.Modules)
    [F.IsQuasicoherent] [G.IsQuasicoherent] (T : AlgebraicSpace S),
    AlgebraicGeometry.AlgebraicSpace.Modules.SpaceHom f F G T →
      (AlgebraicSpace.toSheaf.obj T ⟶
        AlgebraicGeometry.AlgebraicSpace.Modules.homSheaf f F G))
