module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.WeaklyAssociatedPoints.Support
import StacksCheckRecall

/-!
# Lemma 71.2.3

The weakly associated locus of a quasi-coherent module on an algebraic space is
contained in the support of that module.
-/

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules

universe u

/- Lemma 71.2.3: for a scheme `S`, an algebraic space `X` over `S`, and a
quasi-coherent `𝒪_X`-module `F`, the weakly associated locus of `F` is contained
in the support of `F`. -/
@[stacks 0CTY] #check (AlgebraicGeometry.AlgebraicSpace.Modules.weakAss_subset_support :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} (F : X.Modules) [F.IsQuasicoherent],
    F.weakAss ⊆ F.moduleSupport)
