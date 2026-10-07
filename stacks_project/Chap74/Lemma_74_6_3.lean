module

public import stacks_project.Chap74.Lemma_74_6_3_Flat
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace

universe u v

/- Lemma 74.6.3: a quasi-coherent module `F` on an algebraic space `X` over a
scheme `S` is a flat `𝒪_X`-module if its pullbacks along an fpqc covering family
are flat. -/
@[stacks 060W] #check
  (AlgebraicGeometry.AlgebraicSpace.Modules.IsFlat.of_fpqcCovering :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} {ι : Type v}
      (F : X.Modules) [F.IsQuasicoherent]
      (family : ι → Over X), FpqcCovering family →
      (∀ i : ι, ((Modules.pullback (family i).hom).obj F).IsFlat) →
      F.IsFlat)
