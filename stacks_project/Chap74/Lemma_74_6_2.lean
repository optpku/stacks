module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.FinitePresentation.Descent
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace

universe u v

/- Lemma 74.6.2: a quasi-coherent module `ℱ` on an algebraic space `X` over a
scheme `S` is of finite presentation if its pullbacks along an fpqc covering
family are of finite presentation. -/
@[stacks 060V] #check (AlgebraicGeometry.AlgebraicSpace.Modules.IsFinitePresentation.of_fpqcCovering :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} {ι : Type v}
    (ℱ : X.Modules) [ℱ.IsQuasicoherent]
    (family : ι → Over X) (hfamily : FpqcCovering family)
    (hpullback :
      ∀ i : ι, ((Modules.pullback (family i).hom).obj ℱ).IsFinitePresentation),
    ℱ.IsFinitePresentation)
