module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.HomFunctor.Representability

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules

universe u

/- Lemma 99.3.9: For finite-type quasi-coherent modules `F` and `G`, if the base is
Noetherian, `f` is locally of finite type and quasi-separated, and `G` is flat over
the base with proper support, the Hom functor is affine and of finite presentation
over the base. -/
@[stacks 08JY] #check (AlgebraicGeometry.AlgebraicSpace.Modules.homFunctor_isAffineFinitePresentation :
    ∀ {S : Scheme.{u}} {X B : AlgebraicSpace S} (f : X ⟶ B)
    [LocallyOfFiniteType f] [QuasiSeparated f] [IsNoetherian B]
    (F G : X.Modules) [F.IsQuasicoherent] [G.IsQuasicoherent]
    [F.IsFiniteType] [G.IsFiniteType] (hG_flat : flatOver G f)
    (hG_support : Proper ((ClosedSubspaceStructure.reduced (closedSupport G)).ι ≫ f)),
    IsAffineFinitePresentationOver (homFunctor f F G))
