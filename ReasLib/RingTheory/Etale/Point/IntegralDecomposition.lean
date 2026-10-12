/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.TensorProduct.Basic
public import ReasLib.RingTheory.Etale.Point
public import ReasLib.RingTheory.Ideal.ResidueField.SeparableClosure
public import ReasLib.RingTheory.Integral.Decomposition.PurelyInseparable

@[expose] public section

/-!
# Integral decompositions after a pointed étale extension

This file states when an integral algebra acquires a finite product
decomposition with purely inseparable selected residue extensions after a
pointed étale base change.
-/

universe u v

open scoped TensorProduct

namespace PrimeSpectrum.EtalePoint

/-- An integral algebra with finite prime fiber and finite maximal separable
residue subextensions admits, after a pointed étale base change, a finite
product decomposition into integral singleton-fiber factors whose selected
residue extensions are purely inseparable. -/
@[stacks 0BSR]
theorem exists_integralDecomposition
    {R : Type u} [CommRing R] {S : Type v} [CommRing S] [Algebra R S]
    [Algebra.IsIntegral R S] (p : PrimeSpectrum R)
    (h_finite : (p.asIdeal.primesOver S).Finite)
    (h_sep : ∀ q : p.asIdeal.primesOver S,
      Ideal.ResidueField.FiniteSeparablePart p.asIdeal q.1) :
    ∃ U : EtalePoint.{u, u} p,
      ∃ D : PrimeSpectrum.IntegralDecomposition U.point
        (U.carrier ⊗[R] S),
        D.HasPurelyInseparableResidueFields := sorry

end PrimeSpectrum.EtalePoint
