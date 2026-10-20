module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.AlgebraicSpace.Blowup.ExceptionalDivisor

/-!
# Lemma 71.17.4

Closed subspaces correspond to quasi-coherent ideal sheaves through
`ClosedSubspace.idealSheaf` and `ClosedSubspace.ofQuasiCoherentIdeal`.
Thus the ideal-sheaf formulation below applies to every closed center; its exceptional
subspace is the inverse image of that center under the actual Rees blowup.
-/

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

/- Lemma 71.17.4: a blowup is an isomorphism off its center, its exceptional divisor is
 effective Cartier, and its negative first twist is canonically the associated divisor sheaf. -/
@[stacks 085T] #check
  (AlgebraicGeometry.AlgebraicSpace.Blowup.properties :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} {I : IdealSubobject X}
      [IsQuasiCoherent I] (π : Blowup X I),
      IsIso (openInverseImageTo π.hom (closedImmersionComplementι (subschemeι I))) ∧
        ∃ hE : IsEffectiveCartierDivisor (Blowup.exceptionalDivisor π).ι,
          ∃! e : π.reesTwist.twistModule (-1) ≅ Blowup.exceptionalAssociatedSheaf π hE,
            ∃ e1 : Hom.idealSheaf (Blowup.exceptionalDivisor π).ι ≅
                π.reesTwist.twistModule 1,
              Blowup.IsExceptionalTwistComparison π hE e e1)
