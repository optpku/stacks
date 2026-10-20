module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.RepresentableHigherDirectImage
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules CategoryTheory.Limits

universe u

-- Local instance justification (defeq pin): `HasInjectiveResolutions` and `higherDirectImage` pin the Abelian-induced `Preadditive`/`HasZeroMorphisms` instances for defeq of `representableHigherDirectImageIso`.
attribute [local instance 2000] Abelian.toPreadditive Preadditive.preadditiveHasZeroMorphisms

/- 69.3.0.1: Higher direct image of a quasi-coherent module commutes with restriction to
an étale surjective scheme atlas for a representable quasi-compact quasi-separated morphism. -/
@[stacks 071Z] #check (AlgebraicGeometry.AlgebraicSpace.Modules.representableHigherDirectImageIso :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y} (hf : yoneda.relativelyRepresentable f)
    [QuasiCompact f] [QuasiSeparated f] {V : Over S} (g : ofOver V ⟶ Y)
    [Etale g] [Surjective g]
    [Abelian X.Modules] [Abelian Y.Modules]
    [Abelian (ofOver (hf.pullback g)).Modules]
    [Abelian (ofOver V).Modules]
    [HasInjectiveResolutions X.Modules]
    [HasInjectiveResolutions (ofOver (hf.pullback g)).Modules]
    (F : X.Modules) [F.IsQuasicoherent] (i : ℕ),
    (restrictFunctor g).obj (higherDirectImage f F i) ≅
      higherDirectImage (representablePullbackSnd hf g)
        (restrict F (representablePullbackFst hf g)) i)
