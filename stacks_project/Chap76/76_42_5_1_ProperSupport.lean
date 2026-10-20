module

public import stacks_project.Chap66.Lemma_66_12_3
public import stacks_project.Chap67.Definition_67_15_4_SchemeTheoreticSupport
public import stacks_project.Chap67.Definition_67_40_1_Proper
public import stacks_project.Chap67.Lemma_67_31_6_ModuleSupport
public import stacks_project.Chap76.«76_42_2_1_Completion»

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CoherentFormalModule.ProperSupport

/-!
# Completion of coherent modules with proper support on algebraic spaces

Compatibility checks for proper support and the restricted coherent completion
functor. The shared owners provide the module-support and formal-module API.
-/

@[expose] public section

open CategoryTheory Opposite AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

#check (AlgebraicGeometry.AlgebraicSpace.Modules.HasProperSupportOver :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) (F : X.Modules), Prop)

#check (AlgebraicGeometry.AlgebraicSpace.Modules.hasProperSupportOver_iff :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [LocallyOfFiniteType f]
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType],
    Modules.HasProperSupportOver f F ↔
      Proper ((Modules.schemeTheoreticSupport F).ι ≫ f))

#check (AlgebraicGeometry.AlgebraicSpace.Modules.coherentProperSupportCompletionFunctor :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) (I : IdealSubobject X)
    [IsNoetherian X] [LocallyOfFiniteType f] [IsQuasiCoherent I],
    Modules.CoherentProperSupportOver f ⥤ Modules.CoherentFormalProperSupportOver f I)
