module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Quasicoherent.Quotient.Fpqc
import StacksCheckRecall

/-!
# Remark 99.7.3

Kernel-identified quasi-coherent quotients of a module on an algebraic space are
in bijection with compatible families of such quotients along an fpqc covering.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.QCoh CategoryTheory.Limits

noncomputable section

universe u v w

namespace AlgebraicGeometry.AlgebraicSpace.QCoh

/- Remark 99.7.3: restriction gives a bijection between quasi-coherent quotients
and compatible families of quasi-coherent quotients along an fpqc covering,
with agreement tested on the specified fpqc coverings of pairwise fibre products. -/
@[stacks 08IU] #check
  (AlgebraicGeometry.AlgebraicSpace.QCoh.restrictClass_bijective :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}
      {I : Type v} {family : I → Over X} (hfamily : FpqcCovering family)
      {K : I → I → Type w}
      (overlap : ∀ i j, K i j → Over (Limits.pullback (family i).hom (family j).hom))
      (hoverlap : ∀ i j, FpqcCovering (overlap i j))
      (F : X.Modules) [F.IsQuasicoherent],
      Function.Bijective (restrictClass hfamily overlap hoverlap F))

end AlgebraicGeometry.AlgebraicSpace.QCoh
