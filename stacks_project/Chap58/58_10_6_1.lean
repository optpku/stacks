/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.FundamentalGroup.GenericPoint
import StacksCheckRecall

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.Scheme
universe u

/- 58.10.6.1: for an irreducible scheme X, take its actual generic point,
residue field and separable closure. The canonical Galois identification
followed by the generic-point inclusion induces the displayed homomorphism. -/
@[stacks 0BQH]
#check (AlgebraicGeometry.Scheme.genericGaloisMap :
  (X : Scheme.{u}) → [IrreducibleSpace X] →
    ContinuousMonoidHom
      Gal(SeparableClosure (X.residueField (genericPoint X))/X.residueField (genericPoint X))
      (fundamentalGroup (geometricGenericPoint X)))

#check (AlgebraicGeometry.Scheme.genericGaloisEquiv :
  (X : Scheme.{u}) → [IrreducibleSpace X] →
    Gal(SeparableClosure (X.residueField (genericPoint X))/X.residueField (genericPoint X)) ≃*
      fundamentalGroup (separableClosurePoint (X.residueField (genericPoint X))))

#check (AlgebraicGeometry.Scheme.genericPointFundamentalMap :
  (X : Scheme.{u}) → [IrreducibleSpace X] →
    ContinuousMonoidHom
      (fundamentalGroup (separableClosurePoint (X.residueField (genericPoint X))))
      (fundamentalGroup (geometricGenericPoint X)))

#check (AlgebraicGeometry.Scheme.genericGaloisEquiv_isHomeomorph :
  (X : Scheme.{u}) → [IrreducibleSpace X] → IsHomeomorph (genericGaloisEquiv X))

#check (AlgebraicGeometry.Scheme.genericGaloisMap_eq_comp :
  (X : Scheme.{u}) → [IrreducibleSpace X] →
    (genericGaloisMap X).toMonoidHom =
      (genericPointFundamentalMap X).toMonoidHom.comp (genericGaloisEquiv X).toMonoidHom)
