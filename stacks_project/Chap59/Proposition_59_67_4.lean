module

public import ReasLib.FieldTheory.Galois.Cohomology.BrauerVanishing
import StacksCheckRecall

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Action.ModuleCat

/- Proposition 59.67.4 (1): if `Br(K')` is trivial for every finite extension `K'` of a field
`K` with separable algebraic closure `Ksep`, then the continuous cohomology
`DiscreteModuleCat.continuousCohomology (Gal(Ksep/K)) (unitsModule K Ksep) q` vanishes for
every `q ≥ 1`. -/
@[stacks 03R8] #check (GaloisCohomology.unitsCohomologyIsZeroOfFiniteBrauer :
    ∀ (K Ksep : Type u) [Field K] [Field Ksep] [Algebra K Ksep] [IsSepClosure K Ksep]
    (hBr : ∀ (K' : Type u) [Field K'] [Algebra K K'] [FiniteDimensional K K'],
      Subsingleton (Br(K')))
    (q : ℕ) (hq : 1 ≤ q),
    IsZero
      (DiscreteModuleCat.continuousCohomology (Gal(Ksep/K))
        (GaloisCohomology.unitsModule K Ksep) q))

/- Proposition 59.67.4 (2): if `Br(K')` is trivial for every finite extension `K'` of a field
`K` with separable algebraic closure `Ksep`, then for every torsion discrete
`Gal(Ksep/K)`-module `M` the continuous cohomology
`DiscreteModuleCat.continuousCohomology (Gal(Ksep/K)) M q` vanishes for every `q ≥ 2`. -/
@[stacks 03R8] #check (GaloisCohomology.torsionCohomologyIsZeroOfFiniteBrauer :
    ∀ (K Ksep : Type u) [Field K] [Field Ksep] [Algebra K Ksep] [IsSepClosure K Ksep]
    (hBr : ∀ (K' : Type u) [Field K'] [Algebra K K'] [FiniteDimensional K K'],
      Subsingleton (Br(K')))
    (M : DiscreteModuleCat ℤ (Gal(Ksep/K))) (hM : Module.IsTorsion ℤ M.obj.V)
    (q : ℕ) (hq : 2 ≤ q),
    IsZero (DiscreteModuleCat.continuousCohomology (Gal(Ksep/K)) M q))

end
