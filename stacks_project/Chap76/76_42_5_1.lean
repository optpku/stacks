module

public import stacks_project.Chap76.«76_42_5_1_ProperSupport»

@[expose] public section

open AlgebraicGeometry AlgebraicSpace CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- 76.42.5.1: in Situation 76.42.5, the unrestricted completion
`F ↦ (n ↦ F / I^n F)` restricts to a functor from coherent `𝒪_X`-modules with
support proper over the base to coherent formal modules along `I` whose first
stage has support proper over the base. -/
@[stacks 08B8]
noncomputable abbrev coherentProperSupportCompletionFunctor
    {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) (I : IdealSubobject X)
    [IsNoetherian X] [LocallyOfFiniteType f] [IsQuasiCoherent I] :
    Modules.CoherentProperSupportOver f ⥤
      Modules.CoherentFormalProperSupportOver f I :=
  Modules.coherentProperSupportCompletionFunctor f I

/-- The restricted completion of a coherent module with proper support over `f`
is a coherent formal module whose first stage has proper support over `f`. -/
theorem coherentProperSupportCompletionFunctor_obj_property
    {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) (I : IdealSubobject X)
    [IsNoetherian X] [LocallyOfFiniteType f] [IsQuasiCoherent I]
    (ℱ : Modules.CoherentProperSupportOver f) :
    Modules.HasProperSupportOver f
      (Modules.coherentFormalModuleStage
        ((coherentProperSupportCompletionFunctor f I).obj ℱ).obj 1).obj :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
