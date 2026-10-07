module

public import stacks_project.Chap77.Lemma_77_7_9_Sheaf
public import stacks_project.Chap77.Lemma_77_7_9_Limit
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory Opposite

universe u

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) (ℱ : X.Modules)

section

variable [ℱ.IsQuasicoherent]

/- Lemma 77.7.9 (1): In Situation 77.7.8, the functor `F_flat` satisfies the
sheaf property for the fpqc topology. -/
@[stacks 0CWZ] #check
  (Modules.Flattening.functor_isSheaf_fpqc f ℱ :
    Presheaf.IsSheaf (SchemeOver.fpqcTopology Y)
      (Modules.Flattening.functor f ℱ))

end

section

variable [QuasiCompact f] [LocallyOfFinitePresentation f] [ℱ.IsFinitePresentation]

/- Lemma 77.7.9 (2): if `f` is quasi-compact and locally of finite presentation
and `ℱ` is of finite presentation, the flattening functor is limit preserving. -/
@[stacks 0CWZ] #check
  (Modules.Flattening.functor_preservesDirectedAffineLimits f ℱ :
    SchemeOver.PreservesDirectedAffineLimits Y
      (Modules.Flattening.functor f ℱ))

end
