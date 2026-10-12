/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Descent.StandardFpqc
import StacksCheckRecall

@[expose] public section

universe u

/- Lemma 35.5.1 (1): every quasi-coherent descent datum on a standard fpqc cover of an
affine scheme is effective. -/
@[stacks 023S] #check
  (AlgebraicGeometry.Scheme.QCoh.StandardFpqcCover.DescentData.isEffective :
    ∀ {S : AlgebraicGeometry.Scheme.{u}}
      (𝒰 : AlgebraicGeometry.StandardFpqcCover S)
      (D : AlgebraicGeometry.Scheme.QCoh.DescentData 𝒰.U 𝒰.map),
      AlgebraicGeometry.Scheme.QCoh.DescentData.IsEffective D)

/- Lemma 35.5.1 (2): restriction from global quasi-coherent modules to descent data on a
standard fpqc cover is fully faithful. -/
@[stacks 023S] #check
  (AlgebraicGeometry.Scheme.QCoh.StandardFpqcCover.canonicalFunctor.fullyFaithful :
    ∀ {S : AlgebraicGeometry.Scheme.{u}}
      (𝒰 : AlgebraicGeometry.StandardFpqcCover S),
      Nonempty
        (AlgebraicGeometry.Scheme.QCoh.canonicalFunctor 𝒰.U 𝒰.map).FullyFaithful)
