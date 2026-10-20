module

public import stacks_project.Chap66.Lemma_66_29_2_Pullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.InverseImage
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

/- Pullback along a morphism of algebraic spaces preserves quasi-coherent module sheaves. -/
#check (AlgebraicGeometry.AlgebraicSpace.Modules.pullback_isQuasicoherent :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (F : Y.Modules) [F.IsQuasicoherent],
    ((AlgebraicGeometry.AlgebraicSpace.Modules.pullback f).obj F).IsQuasicoherent)

/- Lemma 66.29.2: pullback along a morphism of algebraic spaces over a scheme preserves
quasi-coherent sheaves. -/
@[stacks 03GA] #check
  (AlgebraicGeometry.AlgebraicSpace.Modules.pullback_quasiCoherentModuleProperty :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) {F : Y.Modules},
      F.IsQuasicoherent →
        ((AlgebraicGeometry.AlgebraicSpace.Modules.pullback f).obj F).IsQuasicoherent)

end AlgebraicGeometry.AlgebraicSpace.Modules
