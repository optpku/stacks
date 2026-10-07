module

public import stacks_project.Chap77.Lemma_77_3_6_Purity
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

/- Lemma 77.3.6 (1): a finite type quasicoherent module whose support is proper over
the base is universally pure relative to the base. -/
@[stacks 0CVI] #check
  (AlgebraicGeometry.AlgebraicSpace.Modules.isUniversallyPureOver_of_hasProperSupportOver :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [FiniteType f]
      [Decent f] (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType]
      [Proper ((schemeTheoreticSupport F).ι ≫ f)],
      F.IsUniversallyPureOver f)

/- Lemma 77.3.6 (2): a finite type quasicoherent module on the source of a proper
morphism is universally pure relative to the target. -/
@[stacks 0CVI] #check
  (AlgebraicGeometry.AlgebraicSpace.Modules.isUniversallyPureOver_of_isProper :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Proper f]
      [Decent f] (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType],
      F.IsUniversallyPureOver f)

end AlgebraicGeometry.AlgebraicSpace.Modules

namespace AlgebraicGeometry.AlgebraicSpace

/- Lemma 77.3.6 (3): the source of a proper morphism is universally pure relative
to the target, via its structure sheaf. -/
@[stacks 0CVI] #check
  (AlgebraicGeometry.AlgebraicSpace.isUniversallyPureOver_of_isProper :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Proper f]
      [Decent f],
      Modules.IsUniversallyPureOver
        (SheafOfModules.unit (structureSheaf X) : X.Modules) f)

end AlgebraicGeometry.AlgebraicSpace
