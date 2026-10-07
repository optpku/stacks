module

public import ReasLib.Algebra.CentralSimple.BrauerGroup.GaloisCohomology
import StacksCheckRecall

@[expose] public section

universe u v

open scoped MatrixGroups

/- Lemma 59.61.5: for a field `K`, a separable algebraic closure `Ksep`, and
the Krull-topological Galois group `G` of `Ksep/K`, isomorphism classes of
central simple `K`-algebras of positive degree `d` are in bijection with
continuous non-abelian `H¹` of `G` with discrete coefficients `PGL(d, Ksep)`. -/
@[stacks 03R6] #check
  (CSA.degreeAlgebraClasses_equiv_continuousNonabelianH1 :
    ∀ {K : Type u} [Field K] {Ksep : Type v} [Field Ksep]
      [Algebra K Ksep] [IsSepClosure K Ksep] (d : ℕ), 0 < d →
      Nonempty
        (CSA.degreeAlgebraClasses.{u, u} (K := K) d ≃
          GroupCohomology.continuousNonabelianH1 (G := Gal(Ksep / K)) (A := PGL(d, Ksep))))

end
