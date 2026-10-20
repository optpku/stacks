module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CoherentFormalModule.ProperSupport

@[expose] public section

open AlgebraicGeometry AlgebraicSpace CategoryTheory

universe u

/- 76.42.5.1: in Situation 76.42.5, specialize to the finite-type separated
morphism X → Spec A over a Noetherian I-adically complete ring A, with ideal
sheaf I 𝒪_X. Completion by ideal-power quotients restricts from coherent modules
with proper support over A to coherent formal modules whose first stage has
proper support over A. -/
@[stacks 08B8] #check
  (AlgebraicGeometry.AlgebraicSpace.Modules.coherentProperSupportCompletionFunctor :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) (I : IdealSubobject X)
      [IsNoetherian X] [LocallyOfFiniteType f] [IsQuasiCoherent I],
      Modules.CoherentProperSupportOver f ⥤ Modules.CoherentFormalProperSupportOver f I)
