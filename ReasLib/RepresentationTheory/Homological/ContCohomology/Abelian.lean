module

public import Mathlib.Algebra.Category.Grp.Ulift
public import Mathlib.RepresentationTheory.Homological.ContCohomology.Functoriality
public import ReasLib.RepresentationTheory.Continuous.TopRep

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace ContinuousCohomology

/-- Ulifted continuous cohomology of a topological integral representation. -/
public def abelian (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (A : TopRep ℤ G) (n : ℕ) : AddCommGrpCat.{u + 1} :=
  AddCommGrpCat.uliftFunctor.{u + 1, u}.obj (AddCommGrpCat.of (continuousCohomology n A : Type u))

/-- The map induced on ulifted continuous cohomology by a representation map. -/
public def abelianMap {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {A B : TopRep ℤ G} (f : A ⟶ B) (n : ℕ) : abelian G A n ⟶ abelian G B n :=
  AddCommGrpCat.uliftFunctor.{u + 1, u}.map
    (AddCommGrpCat.ofHom
      ((ContinuousCohomology.map (ContinuousMonoidHom.id G) f n).hom.toLinearMap.toAddMonoidHom))

/-- The induced scalar action on continuous cohomology is unital. -/
theorem adic_smul_one (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {Λ : Type u} [CommRing Λ] (I : Ideal Λ) (M : Type u) [AddCommGroup M] [Module Λ M]
    [IsAdicComplete I M] [DistribMulAction G M] [SMulCommClass G Λ M]
    [hcont : @ContinuousSMul G M _ _ (Ideal.adicModuleTopology I M)] (n : ℕ)
    (x : abelian G (ContinuousModule.adicTopRep G I M) n) :
    abelianMap (ContinuousModule.adicTopRep_smul G I M 1) n x = x := sorry

/-- The induced scalar action on continuous cohomology is associative. -/
theorem adic_smul_mul (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {Λ : Type u} [CommRing Λ] (I : Ideal Λ) (M : Type u) [AddCommGroup M] [Module Λ M]
    [IsAdicComplete I M] [DistribMulAction G M] [SMulCommClass G Λ M]
    [hcont : @ContinuousSMul G M _ _ (Ideal.adicModuleTopology I M)] (n : ℕ)
    (r s : Λ) (x : abelian G (ContinuousModule.adicTopRep G I M) n) :
    abelianMap (ContinuousModule.adicTopRep_smul G I M (r * s)) n x =
      abelianMap (ContinuousModule.adicTopRep_smul G I M r) n
        (abelianMap (ContinuousModule.adicTopRep_smul G I M s) n x) := sorry

/-- The induced scalar action on continuous cohomology preserves zero. -/
theorem adic_smul_zero (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {Λ : Type u} [CommRing Λ] (I : Ideal Λ) (M : Type u) [AddCommGroup M] [Module Λ M]
    [IsAdicComplete I M] [DistribMulAction G M] [SMulCommClass G Λ M]
    [hcont : @ContinuousSMul G M _ _ (Ideal.adicModuleTopology I M)] (n : ℕ) (r : Λ) :
    abelianMap (ContinuousModule.adicTopRep_smul G I M r) n 0 = 0 := sorry

/-- The induced scalar action on continuous cohomology is additive in cohomology classes. -/
theorem adic_smul_add (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {Λ : Type u} [CommRing Λ] (I : Ideal Λ) (M : Type u) [AddCommGroup M] [Module Λ M]
    [IsAdicComplete I M] [DistribMulAction G M] [SMulCommClass G Λ M]
    [hcont : @ContinuousSMul G M _ _ (Ideal.adicModuleTopology I M)] (n : ℕ) (r : Λ)
    (x y : abelian G (ContinuousModule.adicTopRep G I M) n) :
    abelianMap (ContinuousModule.adicTopRep_smul G I M r) n (x + y) =
      abelianMap (ContinuousModule.adicTopRep_smul G I M r) n x +
        abelianMap (ContinuousModule.adicTopRep_smul G I M r) n y := sorry

/-- The induced scalar action on continuous cohomology is additive in scalars. -/
theorem adic_add_smul (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {Λ : Type u} [CommRing Λ] (I : Ideal Λ) (M : Type u) [AddCommGroup M] [Module Λ M]
    [IsAdicComplete I M] [DistribMulAction G M] [SMulCommClass G Λ M]
    [hcont : @ContinuousSMul G M _ _ (Ideal.adicModuleTopology I M)] (n : ℕ)
    (r s : Λ) (x : abelian G (ContinuousModule.adicTopRep G I M) n) :
    abelianMap (ContinuousModule.adicTopRep_smul G I M (r + s)) n x =
      abelianMap (ContinuousModule.adicTopRep_smul G I M r) n x +
        abelianMap (ContinuousModule.adicTopRep_smul G I M s) n x := sorry

/-- The zero scalar acts trivially on continuous cohomology. -/
theorem adic_zero_smul (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {Λ : Type u} [CommRing Λ] (I : Ideal Λ) (M : Type u) [AddCommGroup M] [Module Λ M]
    [IsAdicComplete I M] [DistribMulAction G M] [SMulCommClass G Λ M]
    [hcont : @ContinuousSMul G M _ _ (Ideal.adicModuleTopology I M)] (n : ℕ)
    (x : abelian G (ContinuousModule.adicTopRep G I M) n) :
    abelianMap (ContinuousModule.adicTopRep_smul G I M 0) n x = 0 := sorry

/-- The adic coefficient representation carries its induced scalar action on cohomology. -/
public instance module_abelian_adic (G : Type u) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] {Λ : Type u} [CommRing Λ] (I : Ideal Λ) (M : Type u)
    [AddCommGroup M] [Module Λ M] [IsAdicComplete I M] [DistribMulAction G M]
    [SMulCommClass G Λ M]
    [hcont : @ContinuousSMul G M _ _ (Ideal.adicModuleTopology I M)] (n : ℕ) :
    Module Λ (abelian G (ContinuousModule.adicTopRep G I M) n) where
  smul r x := abelianMap (ContinuousModule.adicTopRep_smul G I M r) n x
  one_smul := adic_smul_one G I M n
  mul_smul := adic_smul_mul G I M n
  smul_zero := adic_smul_zero G I M n
  smul_add := adic_smul_add G I M n
  add_smul := adic_add_smul G I M n
  zero_smul := adic_zero_smul G I M n

end ContinuousCohomology

end
