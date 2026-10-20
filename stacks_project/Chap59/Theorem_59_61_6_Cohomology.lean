module

public import ReasLib.FieldTheory.Galois.Cohomology.Units

@[expose] public section

universe u v

open CategoryTheory
open CategoryTheory.Action
open CategoryTheory.Action.ModuleCat

variable (K : Type u) (Ksep : Type v) [Field K] [Field Ksep]
variable [Algebra K Ksep] [IsSepClosure K Ksep]

#check (GaloisCohomology.unitsModule K Ksep : DiscreteModuleCat ℤ (Gal(Ksep / K)))

#check (GaloisCohomology.unitsModule_obj K Ksep :
  (GaloisCohomology.unitsModule K Ksep).obj.V = ModuleCat.of ℤ (Additive Ksepˣ))

#check (GaloisCohomology.unitsModule_rho K Ksep : ∀ σ : Gal(Ksep / K),
  (GaloisCohomology.unitsModule K Ksep).obj.ρ σ = ModuleCat.ofHom
    ((MulDistribMulAction.toMonoidHom (A := Ksepˣ) σ).toAdditive.toIntLinearMap))

#check (GaloisCohomology.h2Units K Ksep : Type v)

#check (GaloisCohomology.h2Units_def K Ksep :
  GaloisCohomology.h2Units K Ksep = _root_.continuousCohomology 2
    (DiscreteModuleCat.toTopRep (Gal(Ksep / K)) (GaloisCohomology.unitsModule K Ksep)))

end
