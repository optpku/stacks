module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Cohomology.Field
public import ReasLib.FieldTheory.Galois.Cohomology.Vanishing
public import ReasLib.AlgebraicGeometry.Scheme.Module.Picard.Cohomology
public import ReasLib.AlgebraicGeometry.Scheme.Module.Picard.UniqueFactorization
public import ReasLib.AlgebraicGeometry.Scheme.Module.Cohomology.Affine
public import ReasLib.AlgebraicGeometry.Scheme.Module.Quasicoherent
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open CategoryTheory.Action ModuleCat
open AlgebraicGeometry
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.Etale.Small

universe u

noncomputable section

section Field

variable (K Ksep : Type u) [Field K] [Field Ksep]
  [Algebra K Ksep] [IsSepClosure K Ksep]

/- Example 59.59.3 (1): the geometric stalk of the constant `ZMod n` sheaf is the
constant discrete Galois module with trivial action. -/
@[stacks 03QV] #check
  (GaloisCohomology.constantZModEtaleStalk K Ksep : ∀ (n : ℕ)
    [HasWeakSheafify (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u}],
    IsIsomorphic
      (GaloisCohomology.etaleStalk K Ksep
        ((constantSheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u}).obj
          (AddCommGrpCat.of (ULift.{u} (ZMod n)))))
      (GaloisCohomology.constantZModModule K Ksep n))

/- Example 59.59.3 (2): the geometric stalk of `G_m` is `Ksepˣ` with its natural
Galois action, written additively. -/
@[stacks 03QV] #check
  (GaloisCohomology.unitsEtaleStalk K Ksep :
    IsIsomorphic
      (GaloisCohomology.etaleStalk K Ksep (unitsAddSheaf (Spec (.of K))))
      (GaloisCohomology.unitsModule K Ksep))

/- Example 59.59.3 (3): the geometric stalk of `G_a` is the additive Galois module
on `Ksep`. -/
@[stacks 03QV] #check
  (GaloisCohomology.additiveEtaleStalk K Ksep :
    IsIsomorphic
      (GaloisCohomology.etaleStalk K Ksep
        ((sheafCompose (Spec (.of K)).smallEtaleTopology
          (forget₂ RingCat AddCommGrpCat)).obj (structureSheaf (Spec (.of K)))))
      (GaloisCohomology.additiveModule K Ksep))

/- Example 59.59.3 (4): the geometric stalk of `mu_n` is the additive presentation of
`rootsOfUnity n Ksep` with its natural Galois action. -/
@[stacks 03QV] #check
  (GaloisCohomology.rootsOfUnityEtaleStalk K Ksep : ∀ n : ℕ,
    IsIsomorphic
      (GaloisCohomology.etaleStalk K Ksep
        (kernel (n • 𝟙 (unitsAddSheaf (Spec (.of K))))))
      (GaloisCohomology.rootsOfUnityModule K Ksep n))

end Field

/- Example 59.59.3 (5): degree-zero étale cohomology of `G_m` is the additive
group of global units. -/
@[stacks 03QV] #check
  (AlgebraicGeometry.Scheme.h0EtaleUnitsIsomorphicGlobalUnits : ∀ (S : Scheme.{u})
    [HasSheafify S.smallEtaleTopology AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf S.smallEtaleTopology AddCommGrpCat.{u})],
    IsIsomorphic
      ((Sheaf.functorH S.smallEtaleTopology 0).obj (Etale.Small.unitsAddSheaf S))
      (AddCommGrpCat.of (Additive Γ(S, ⊤)ˣ)))

/- Example 59.59.3 (6): first étale cohomology of `G_m`, lifted to the Picard
group's universe, is the Picard group. -/
@[stacks 03QV] #check
  (AlgebraicGeometry.Scheme.h1EtaleUnitsIsomorphicPicard : ∀ (S : Scheme.{u})
    [HasSheafify S.smallEtaleTopology AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf S.smallEtaleTopology AddCommGrpCat.{u})],
    IsIsomorphic
      ((AddCommGrpCat.uliftFunctor.{u + 1, u}).obj
        ((Sheaf.functorH S.smallEtaleTopology 1).obj (Etale.Small.unitsAddSheaf S)))
      (AddCommGrpCat.of S.PicardGroup))

/- Example 59.59.3 (7): étale and Zariski cohomology of the additive structure
sheaf are isomorphic in every degree. -/
@[stacks 03QV] #check
  (AlgebraicGeometry.Scheme.etaleAdditiveCohomologyIsomorphicZariski :
    ∀ (S : Scheme.{u}) (i : ℕ)
    [HasSheafify S.smallEtaleTopology AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf S.smallEtaleTopology AddCommGrpCat.{u})]
    [HasSheafify S.smallZariskiTopology AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf S.smallZariskiTopology AddCommGrpCat.{u})],
    IsIsomorphic
      ((Sheaf.functorH S.smallEtaleTopology i).obj
        ((sheafCompose S.smallEtaleTopology (forget₂ RingCat AddCommGrpCat)).obj
          (Etale.Small.structureSheaf S)))
      ((Sheaf.functorH S.smallZariskiTopology i).obj
        ((sheafCompose S.smallZariskiTopology (forget₂ RingCat AddCommGrpCat)).obj
          (Zariski.Small.structureSheaf S))))

/- Example 59.59.3 (8): étale and Zariski cohomology agree for the sheaves
associated to a quasi-coherent module. -/
@[stacks 03QV] #check
  (AlgebraicGeometry.Scheme.quasicoherentEtaleCohomologyIsomorphicZariski :
    ∀ (S : Scheme.{u}) (F : S.Modules) [F.IsQuasicoherent] (i : ℕ)
    [HasSheafify S.smallEtaleTopology AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf S.smallEtaleTopology AddCommGrpCat.{u})]
    [HasSheafify S.smallZariskiTopology AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf S.smallZariskiTopology AddCommGrpCat.{u})],
    IsIsomorphic
      ((Sheaf.functorH S.smallEtaleTopology i).obj
        ((SheafOfModules.toSheaf (AssociatedModule.smallStructureSheaf .etale S)).obj
          (AssociatedModule.small .etale S F)))
      ((Sheaf.functorH S.smallZariskiTopology i).obj
        ((SheafOfModules.toSheaf (AssociatedModule.smallStructureSheaf .zariski S)).obj
          (AssociatedModule.small .zariski S F))))

section Field

variable (K Ksep : Type u) [Field K] [Field Ksep]
  [Algebra K Ksep] [IsSepClosure K Ksep]

/- Example 59.59.3 (9): first derived-invariants cohomology of the absolute Galois
group with coefficients in `Ksepˣ` vanishes, i.e. Hilbert's theorem 90. -/
@[stacks 03QV] #check
  (GaloisCohomology.hilbert90 K Ksep :
    IsZero ((DiscreteModuleCat.derivedCohomologyFunctor ℤ (Gal(Ksep / K)) 1).obj
      (GaloisCohomology.unitsModule K Ksep)))

/- Example 59.59.3 (10): positive-degree derived-invariants Galois cohomology of the
additive module `Ksep` vanishes. -/
@[stacks 03QV] #check
  (GaloisCohomology.additiveCohomologyIsZero K Ksep : ∀ (i : ℕ) (hi : 0 < i),
    IsZero ((DiscreteModuleCat.derivedCohomologyFunctor ℤ (Gal(Ksep / K)) i).obj
      (GaloisCohomology.additiveModule K Ksep)))

end Field

/- The Zariski degree-one units cohomology link in the Picard comparison. -/
#check (AlgebraicGeometry.Scheme.picardEquivUnitsH1 : ∀ (S : Scheme.{u})
  [HasSheafify (Opens.grothendieckTopology S.toRingedSpace) AddCommGrpCat.{u}]
  [HasExt.{u} (Sheaf (Opens.grothendieckTopology S.toRingedSpace) AddCommGrpCat.{u})],
  S.PicardGroup ≃+ (CategoryTheory.Sheaf.unitsAddSheaf S.toRingedSpace.sheaf).H 1)

variable (K : Type u) [Field K]

/- The Picard group of the spectrum of a field is trivial. -/
#check (AlgebraicGeometry.Scheme.subsingleton_picardGroup_Spec_of_uniqueFactorizationMonoid K :
  Subsingleton (Spec (.of K)).PicardGroup)

/- The positive-degree structure-module cohomology of the spectrum of a field vanishes. -/
#check (AlgebraicGeometry.Scheme.higherCohomology_isZero_of_isAffine
  (SheafOfModules.unit (Spec (.of K)).ringCatSheaf) :
  ∀ (i : ℕ) (hi : 0 < i),
  IsZero (((SheafOfModules.toSheaf (Spec (.of K)).ringCatSheaf).obj
    (SheafOfModules.unit (Spec (.of K)).ringCatSheaf)).H' i (⊤ : (Spec (.of K)).Opens)))

end
