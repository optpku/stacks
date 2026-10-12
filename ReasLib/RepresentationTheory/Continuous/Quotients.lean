/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.RepresentationTheory.Rep.Basic
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
public import Mathlib.Topology.Algebra.OpenSubgroup
public import ReasLib.CategoryTheory.Action.ModuleCat.OpenStabilizer.Definition

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.Action.ModuleCat

noncomputable section

universe u

namespace ContinuousModule

/-- The open-stabilizer construction turns an additive continuous action into a
discrete continuous integral module. -/
def ofAddGModule (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (M : Type u) [AddCommGroup M] [DistribMulAction G M]
    (h : ∀ x : M, IsOpen (MulAction.stabilizer G x : Set G)) :
    DiscreteModuleCat ℤ G :=
  ⟨{ V := ModuleCat.of ℤ M
     ρ :=
       { toFun := fun g => ModuleCat.ofHom ((Rep.ofDistribMulAction ℤ G M).ρ g)
         map_one' := by
           apply ModuleCat.hom_ext
           apply LinearMap.ext
           intro x
           change (1 : G) • x = x
           exact one_smul G x
         map_mul' := by
           intro g h
           apply ModuleCat.hom_ext
           apply LinearMap.ext
           intro x
           change (g * h) • x = g • h • x
           exact mul_smul g h x } }, h⟩

/-- An equivariant additive map induces a morphism of discrete continuous modules. -/
def ofAddGModuleMap (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {M N : Type u} [AddCommGroup M] [AddCommGroup N] [DistribMulAction G M]
    [DistribMulAction G N]
    {hM : ∀ x : M, IsOpen (MulAction.stabilizer G x : Set G)}
    {hN : ∀ x : N, IsOpen (MulAction.stabilizer G x : Set G)} (f : M →+ N)
    (hcomm : ∀ (g : G) (x : M), f (g • x) = g • f x) :
    ofAddGModule G M hM ⟶ ofAddGModule G N hN :=
  ObjectProperty.homMk
    { hom := ModuleCat.ofHom f.toIntLinearMap
      comm := by
        intro g
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro x
        change f (g • x) = g • f x
        exact hcomm g x }

/-- Open finite-index invariant additive subgroups indexing finite continuous
quotients. -/
def IsFiniteGaloisQuotient (G : Type u) [Group G] (M : Type u)
    [AddCommGroup M] [TopologicalSpace M] [DistribMulAction G M] :
    ObjectProperty (OpenAddSubgroup M) :=
  fun U ↦ Finite (M ⧸ U.toAddSubgroup) ∧
    ∀ g : G, AddSubgroup.map (DistribSMul.toAddMonoidHom M g) U.toAddSubgroup = U.toAddSubgroup

/-- Membership in `IsFiniteGaloisQuotient` exposes finiteness and invariance. -/
theorem IsFiniteGaloisQuotient.mem_iff (G : Type u) [Group G] (M : Type u)
    [AddCommGroup M] [TopologicalSpace M] [DistribMulAction G M] (U : OpenAddSubgroup M) :
    IsFiniteGaloisQuotient G M U ↔
      Finite (M ⧸ U.toAddSubgroup) ∧
        ∀ g : G, AddSubgroup.map (DistribSMul.toAddMonoidHom M g) U.toAddSubgroup = U.toAddSubgroup := sorry

/-- Membership of the top subgroup in the finite Galois quotient index. -/
theorem isFiniteGaloisQuotient_top (G : Type u) [Group G] (M : Type u)
    [AddCommGroup M] [TopologicalSpace M] [DistribMulAction G M] :
    IsFiniteGaloisQuotient G M (⊤ : OpenAddSubgroup M) := sorry

/-- The top open subgroup is a finite invariant quotient. -/
def finiteGaloisQuotient_top (G : Type u) [Group G] (M : Type u)
    [AddCommGroup M] [TopologicalSpace M] [DistribMulAction G M] :
    (IsFiniteGaloisQuotient G M).FullSubcategory :=
  ⟨⊤, isFiniteGaloisQuotient_top G M⟩

/-- The adic submodule is open in the adic topology. -/
theorem adicQuotient_isOpen {Λ : Type u} [CommRing Λ] (I : Ideal Λ) (M : Type u)
    [AddCommGroup M] [Module Λ M] (n : ℕ) :
    @IsOpen M (Ideal.adicModuleTopology I M)
      ((I ^ n • (⊤ : Submodule Λ M) : Submodule Λ M) : Set M) := sorry

/-- Invariance of an adic stage under a commuting group action. -/
theorem adicQuotient_mapsTo (G : Type u) [Group G] {Λ : Type u} [CommRing Λ] (I : Ideal Λ)
    (M : Type u) [AddCommGroup M] [Module Λ M] [DistribMulAction G M]
    [SMulCommClass G Λ M] (n : ℕ) (g : G) :
    (I ^ n • (⊤ : Submodule Λ M)).toAddSubgroup ≤
      ((I ^ n • (⊤ : Submodule Λ M)).toAddSubgroup.comap
        (DistribSMul.toAddMonoidHom M g)) := sorry

/-- The induced additive action map on an adic quotient. -/
def adicQuotientSMul (G : Type u) [Group G] {Λ : Type u} [CommRing Λ] (I : Ideal Λ) (M : Type u)
    [AddCommGroup M] [Module Λ M] [DistribMulAction G M] [SMulCommClass G Λ M]
    (n : ℕ) (g : G) : (M ⧸ (I ^ n • (⊤ : Submodule Λ M))) →+
      (M ⧸ (I ^ n • (⊤ : Submodule Λ M))) :=
  QuotientAddGroup.map _ _ (DistribSMul.toAddMonoidHom M g) (adicQuotient_mapsTo G I M n g)

/-- The descended adic action satisfies the identity law. -/
theorem adicQuotientSMul_one (G : Type u) [Group G] {Λ : Type u} [CommRing Λ]
    (I : Ideal Λ) (M : Type u) [AddCommGroup M] [Module Λ M]
    [DistribMulAction G M] [SMulCommClass G Λ M] (n : ℕ) (x : M ⧸ (I ^ n • (⊤ : Submodule Λ M))) :
    adicQuotientSMul G I M n 1 x = x := sorry

/-- The descended adic action satisfies the multiplication law. -/
theorem adicQuotientSMul_mul (G : Type u) [Group G] {Λ : Type u} [CommRing Λ]
    (I : Ideal Λ) (M : Type u) [AddCommGroup M] [Module Λ M]
    [DistribMulAction G M] [SMulCommClass G Λ M] (n : ℕ) (g h : G)
    (x : M ⧸ (I ^ n • (⊤ : Submodule Λ M))) :
    adicQuotientSMul G I M n (g * h) x =
      adicQuotientSMul G I M n g (adicQuotientSMul G I M n h x) := sorry

/-- The descended adic action preserves zero. -/
theorem adicQuotientSMul_zero (G : Type u) [Group G] {Λ : Type u} [CommRing Λ]
    (I : Ideal Λ) (M : Type u) [AddCommGroup M] [Module Λ M]
    [DistribMulAction G M] [SMulCommClass G Λ M] (n : ℕ) (g : G) :
    adicQuotientSMul G I M n g 0 = 0 := sorry

/-- The descended adic action is additive. -/
theorem adicQuotientSMul_add (G : Type u) [Group G] {Λ : Type u} [CommRing Λ]
    (I : Ideal Λ) (M : Type u) [AddCommGroup M] [Module Λ M]
    [DistribMulAction G M] [SMulCommClass G Λ M] (n : ℕ) (g : G)
    (x y : M ⧸ (I ^ n • (⊤ : Submodule Λ M))) :
    adicQuotientSMul G I M n g (x + y) =
      adicQuotientSMul G I M n g x + adicQuotientSMul G I M n g y := sorry

/-- The induced distributive action on an adic quotient. -/
instance adicQuotient_distribMulAction (G : Type u) [Group G] {Λ : Type u} [CommRing Λ]
    (I : Ideal Λ) (M : Type u) [AddCommGroup M] [Module Λ M] [DistribMulAction G M]
    [SMulCommClass G Λ M] (n : ℕ) :
    DistribMulAction G (M ⧸ (I ^ n • (⊤ : Submodule Λ M))) where
  smul g x := adicQuotientSMul G I M n g x
  one_smul := adicQuotientSMul_one G I M n
  mul_smul := adicQuotientSMul_mul G I M n
  smul_zero := adicQuotientSMul_zero G I M n
  smul_add := adicQuotientSMul_add G I M n

/-- Open stabilizers on adic quotients follow from continuity and openness. -/
theorem adicQuotient_openStabilizer (G : Type u) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] {Λ : Type u} [CommRing Λ] (I : Ideal Λ) (M : Type u)
    [AddCommGroup M] [Module Λ M] [DistribMulAction G M] [SMulCommClass G Λ M]
    [hcont : @ContinuousSMul G M _ _ (Ideal.adicModuleTopology I M)] (n : ℕ) :
    ∀ x : M ⧸ (I ^ n • (⊤ : Submodule Λ M)), IsOpen (MulAction.stabilizer G x : Set G) := sorry

/-- The discrete module `M ⧸ I^n M` attached to an adic action. -/
def adicQuotientModule (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {Λ : Type u} [CommRing Λ] (I : Ideal Λ) (M : Type u) [AddCommGroup M] [Module Λ M]
    [DistribMulAction G M] [SMulCommClass G Λ M]
    [hcont : @ContinuousSMul G M _ _ (Ideal.adicModuleTopology I M)] (n : ℕ) :
    DiscreteModuleCat ℤ G :=
  ofAddGModule G (M ⧸ (I ^ n • (⊤ : Submodule Λ M))) (adicQuotient_openStabilizer G I M n)

/-- Kernel inclusion gives the transition map between adic quotients. -/
theorem adicQuotient_le {Λ : Type u} [CommRing Λ] (I : Ideal Λ) (M : Type u)
    [AddCommGroup M] [Module Λ M] {n m : ℕ} (h : n ≤ m) :
    (I ^ m • (⊤ : Submodule Λ M)).toAddSubgroup ≤
      (I ^ n • (⊤ : Submodule Λ M)).toAddSubgroup := sorry

/-- Adic quotient transitions commute with the induced group action. -/
theorem adicQuotient_transition_equivariant (G : Type u) [Group G] {Λ : Type u}
    [CommRing Λ] (I : Ideal Λ) (M : Type u) [AddCommGroup M] [Module Λ M]
    [DistribMulAction G M] [SMulCommClass G Λ M] {n m : ℕ} (h : n ≤ m) (g : G)
    (x : M ⧸ (I ^ m • (⊤ : Submodule Λ M))) :
    QuotientAddGroup.map _ _ (AddMonoidHom.id M) (adicQuotient_le I M h)
        (adicQuotientSMul G I M m g x) =
      adicQuotientSMul G I M n g
        (QuotientAddGroup.map _ _ (AddMonoidHom.id M) (adicQuotient_le I M h) x) := sorry

/-- A morphism `n ⟶ m` in `ℕᵒᵖ` induces the equivariant quotient transition
`M/I^(unop n)M → M/I^(unop m)M` between discrete continuous modules. -/
def adicQuotientSystemMap (G : Type u) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] {Λ : Type u} [CommRing Λ] (I : Ideal Λ) (M : Type u)
    [AddCommGroup M] [Module Λ M] [DistribMulAction G M] [SMulCommClass G Λ M]
    [hcont : @ContinuousSMul G M _ _ (Ideal.adicModuleTopology I M)]
    {n m : ℕᵒᵖ} (f : n ⟶ m) :
    adicQuotientModule G I M (unop n) ⟶ adicQuotientModule G I M (unop m) :=
  ofAddGModuleMap G (QuotientAddGroup.map _ _ (AddMonoidHom.id M)
      (adicQuotient_le I M (leOfHom (unop f)))) (by
        intro g x
        exact adicQuotient_transition_equivariant G I M (leOfHom (unop f)) g x)

/-- The adic quotient system preserves identity morphisms. -/
theorem adicQuotientSystem_map_id (G : Type u) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] {Λ : Type u} [CommRing Λ] (I : Ideal Λ) (M : Type u)
    [AddCommGroup M] [Module Λ M] [DistribMulAction G M] [SMulCommClass G Λ M]
    [hcont : @ContinuousSMul G M _ _ (Ideal.adicModuleTopology I M)] (n : ℕᵒᵖ) :
    adicQuotientSystemMap G I M (𝟙 n) = 𝟙 (adicQuotientModule G I M (unop n)) := sorry

/-- The adic quotient system preserves composition of transition morphisms. -/
theorem adicQuotientSystem_map_comp (G : Type u) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] {Λ : Type u} [CommRing Λ] (I : Ideal Λ) (M : Type u)
    [AddCommGroup M] [Module Λ M] [DistribMulAction G M] [SMulCommClass G Λ M]
    [hcont : @ContinuousSMul G M _ _ (Ideal.adicModuleTopology I M)]
    {n m k : ℕᵒᵖ} (f : n ⟶ m) (g : m ⟶ k) :
    adicQuotientSystemMap G I M (f ≫ g) =
      adicQuotientSystemMap G I M f ≫ adicQuotientSystemMap G I M g := sorry

/-- The inverse system of adic quotient modules. -/
def adicQuotientSystem (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {Λ : Type u} [CommRing Λ] (I : Ideal Λ) (M : Type u) [AddCommGroup M] [Module Λ M]
    [DistribMulAction G M] [SMulCommClass G Λ M]
    [hcont : @ContinuousSMul G M _ _ (Ideal.adicModuleTopology I M)] :
    ℕᵒᵖ ⥤ DiscreteModuleCat ℤ G where
  obj n := adicQuotientModule G I M (unop n)
  map f := adicQuotientSystemMap G I M f
  map_id := adicQuotientSystem_map_id G I M
  map_comp := adicQuotientSystem_map_comp G I M

/-- Coefficient scalar multiplication is equivariant on every adic quotient. -/
theorem adicQuotient_scalar_equivariant (G : Type u) [Group G] {Λ : Type u} [CommRing Λ]
    (I : Ideal Λ) (M : Type u) [AddCommGroup M] [Module Λ M] [DistribMulAction G M]
    [SMulCommClass G Λ M] (r : Λ) (n : ℕ) (g : G)
    (x : M ⧸ (I ^ n • (⊤ : Submodule Λ M))) :
    (DistribSMul.toAddMonoidHom (M ⧸ (I ^ n • (⊤ : Submodule Λ M))) r)
        (g • x) = g • (DistribSMul.toAddMonoidHom
          (M ⧸ (I ^ n • (⊤ : Submodule Λ M))) r) x := sorry

/-- Scalar multiplication induces an equivariant endomorphism of each adic quotient. -/
def adicQuotientModule_smul (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {Λ : Type u} [CommRing Λ] (I : Ideal Λ)
    (M : Type u) [AddCommGroup M] [Module Λ M] [DistribMulAction G M]
    [SMulCommClass G Λ M] [hcont : @ContinuousSMul G M _ _ (Ideal.adicModuleTopology I M)]
    (r : Λ) (n : ℕ) : adicQuotientModule G I M n ⟶ adicQuotientModule G I M n :=
  ofAddGModuleMap G (DistribSMul.toAddMonoidHom (M ⧸ (I ^ n • (⊤ : Submodule Λ M))) r)
    (by
      intro g x
      exact adicQuotient_scalar_equivariant G I M r n g x)

/-- Scalar multiplication commutes with the transition maps of the adic system. -/
theorem adicQuotientSystem_smul_naturality (G : Type u) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] {Λ : Type u} [CommRing Λ] (I : Ideal Λ) (M : Type u)
    [AddCommGroup M] [Module Λ M] [DistribMulAction G M] [SMulCommClass G Λ M]
    [hcont : @ContinuousSMul G M _ _ (Ideal.adicModuleTopology I M)] (r : Λ)
    {n m : ℕᵒᵖ} (f : n ⟶ m) :
    adicQuotientSystemMap G I M f ≫ adicQuotientModule_smul G I M r (unop m) =
      adicQuotientModule_smul G I M r (unop n) ≫ adicQuotientSystemMap G I M f := sorry

/-- The scalar endomorphisms form a natural transformation of the adic system. -/
def adicQuotientSystem_smul (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {Λ : Type u} [CommRing Λ] (I : Ideal Λ) (M : Type u) [AddCommGroup M] [Module Λ M]
    [DistribMulAction G M] [SMulCommClass G Λ M]
    [hcont : @ContinuousSMul G M _ _ (Ideal.adicModuleTopology I M)] (r : Λ) :
    adicQuotientSystem G I M ⟶ adicQuotientSystem G I M where
  app n := adicQuotientModule_smul G I M r (unop n)
  naturality := by
    intro X Y f
    simpa [adicQuotientSystem] using adicQuotientSystem_smul_naturality G I M r f

/-- Inclusion of finite invariant quotients gives a transition map. -/
theorem finiteGaloisQuotient_le (G : Type u) [Group G] (M : Type u)
    [AddCommGroup M] [TopologicalSpace M] [DistribMulAction G M]
    {U V : (IsFiniteGaloisQuotient G M).FullSubcategory} (f : U ⟶ V) :
    U.obj.toAddSubgroup ≤ V.obj.toAddSubgroup := sorry

/-- Invariance of a finite quotient subgroup under the group action. -/
theorem finiteGaloisQuotient_mapsTo (G : Type u) [Group G] (M : Type u)
    [AddCommGroup M] [TopologicalSpace M] [DistribMulAction G M]
    (U : (IsFiniteGaloisQuotient G M).FullSubcategory) (g : G) :
    U.obj.toAddSubgroup ≤
      U.obj.toAddSubgroup.comap (DistribSMul.toAddMonoidHom M g) := sorry

/-- The induced finite quotient action satisfies the identity law. -/
theorem finiteQuotientSMul_one (G : Type u) [Group G] (M : Type u)
    [AddCommGroup M] [TopologicalSpace M] [DistribMulAction G M]
    (U : (IsFiniteGaloisQuotient G M).FullSubcategory)
    (x : M ⧸ U.obj.toAddSubgroup) :
    QuotientAddGroup.map _ _ (DistribSMul.toAddMonoidHom M 1)
      (finiteGaloisQuotient_mapsTo G M U 1) x = x := sorry

/-- The induced finite quotient action satisfies the multiplication law. -/
theorem finiteQuotientSMul_mul (G : Type u) [Group G] (M : Type u)
    [AddCommGroup M] [TopologicalSpace M] [DistribMulAction G M]
    (U : (IsFiniteGaloisQuotient G M).FullSubcategory) (g h : G)
    (x : M ⧸ U.obj.toAddSubgroup) :
    QuotientAddGroup.map _ _ (DistribSMul.toAddMonoidHom M (g * h))
        (finiteGaloisQuotient_mapsTo G M U (g * h)) x =
      QuotientAddGroup.map _ _ (DistribSMul.toAddMonoidHom M g)
        (finiteGaloisQuotient_mapsTo G M U g)
        (QuotientAddGroup.map _ _ (DistribSMul.toAddMonoidHom M h)
          (finiteGaloisQuotient_mapsTo G M U h) x) := sorry

/-- The induced finite quotient action preserves zero. -/
theorem finiteQuotientSMul_zero (G : Type u) [Group G] (M : Type u)
    [AddCommGroup M] [TopologicalSpace M] [DistribMulAction G M]
    (U : (IsFiniteGaloisQuotient G M).FullSubcategory) (g : G) :
    QuotientAddGroup.map _ _ (DistribSMul.toAddMonoidHom M g)
      (finiteGaloisQuotient_mapsTo G M U g) 0 = 0 := sorry

/-- The induced finite quotient action is additive. -/
theorem finiteQuotientSMul_add (G : Type u) [Group G] (M : Type u)
    [AddCommGroup M] [TopologicalSpace M] [DistribMulAction G M]
    (U : (IsFiniteGaloisQuotient G M).FullSubcategory) (g : G)
    (x y : M ⧸ U.obj.toAddSubgroup) :
    QuotientAddGroup.map _ _ (DistribSMul.toAddMonoidHom M g)
      (finiteGaloisQuotient_mapsTo G M U g) (x + y) =
      QuotientAddGroup.map _ _ (DistribSMul.toAddMonoidHom M g)
        (finiteGaloisQuotient_mapsTo G M U g) x +
        QuotientAddGroup.map _ _ (DistribSMul.toAddMonoidHom M g)
          (finiteGaloisQuotient_mapsTo G M U g) y := sorry

/-- The induced action on a finite invariant quotient. -/
instance finiteQuotient_distribMulAction (G : Type u) [Group G] (M : Type u)
    [AddCommGroup M] [TopologicalSpace M] [DistribMulAction G M]
    (U : (IsFiniteGaloisQuotient G M).FullSubcategory) :
    DistribMulAction G (M ⧸ U.obj.toAddSubgroup) where
  smul g x := QuotientAddGroup.map _ _ (DistribSMul.toAddMonoidHom M g)
    (finiteGaloisQuotient_mapsTo G M U g) x
  one_smul := finiteQuotientSMul_one G M U
  mul_smul := finiteQuotientSMul_mul G M U
  smul_zero := finiteQuotientSMul_zero G M U
  smul_add := finiteQuotientSMul_add G M U

/-- Open stabilizers on finite invariant quotients. -/
theorem finiteQuotient_openStabilizer (G : Type u) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (M : Type u) [AddCommGroup M] [TopologicalSpace M]
    [IsTopologicalAddGroup M] [DistribMulAction G M] [ContinuousSMul G M]
    (U : (IsFiniteGaloisQuotient G M).FullSubcategory) :
    ∀ x : M ⧸ U.obj.toAddSubgroup, IsOpen (MulAction.stabilizer G x : Set G) := sorry

/-- The discrete module attached to a finite invariant quotient. -/
def finiteQuotientModule (G : Type u) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (M : Type u) [AddCommGroup M] [TopologicalSpace M]
    [IsTopologicalAddGroup M] [DistribMulAction G M] [ContinuousSMul G M]
    (U : (IsFiniteGaloisQuotient G M).FullSubcategory) : DiscreteModuleCat ℤ G :=
  ofAddGModule G (M ⧸ U.obj.toAddSubgroup) (finiteQuotient_openStabilizer G M U)

/-- Finite quotient transitions commute with the induced group action. -/
theorem finiteQuotient_transition_equivariant (G : Type u) [Group G] (M : Type u)
    [AddCommGroup M] [TopologicalSpace M] [DistribMulAction G M]
    {U V : (IsFiniteGaloisQuotient G M).FullSubcategory} (f : U ⟶ V) (g : G)
    (x : M ⧸ U.obj.toAddSubgroup) :
    QuotientAddGroup.map _ _ (AddMonoidHom.id M) (finiteGaloisQuotient_le G M f)
        (g • x) =
      g • QuotientAddGroup.map _ _ (AddMonoidHom.id M)
        (finiteGaloisQuotient_le G M f) x := sorry

/-- The morphism assigned to a finite quotient transition. -/
def profiniteQuotientSystemMap (G : Type u) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (M : Type u) [AddCommGroup M] [TopologicalSpace M]
    [IsTopologicalAddGroup M] [DistribMulAction G M] [ContinuousSMul G M]
    {U V : (IsFiniteGaloisQuotient G M).FullSubcategory} (f : U ⟶ V) :
    finiteQuotientModule G M U ⟶ finiteQuotientModule G M V :=
  ofAddGModuleMap G
    (QuotientAddGroup.map _ _ (AddMonoidHom.id M) (finiteGaloisQuotient_le G M f)) (by
      intro g x
      exact finiteQuotient_transition_equivariant G M f g x)

/-- The finite quotient system preserves identity morphisms. -/
theorem profiniteQuotientSystem_map_id (G : Type u) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (M : Type u) [AddCommGroup M] [TopologicalSpace M]
    [IsTopologicalAddGroup M] [DistribMulAction G M] [ContinuousSMul G M]
    (U : (IsFiniteGaloisQuotient G M).FullSubcategory) :
    profiniteQuotientSystemMap G M (𝟙 U) = 𝟙 (finiteQuotientModule G M U) := sorry

/-- The finite quotient system preserves composition of transition morphisms. -/
theorem profiniteQuotientSystem_map_comp (G : Type u) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (M : Type u) [AddCommGroup M] [TopologicalSpace M]
    [IsTopologicalAddGroup M] [DistribMulAction G M] [ContinuousSMul G M]
    {U V W : (IsFiniteGaloisQuotient G M).FullSubcategory} (f : U ⟶ V) (g : V ⟶ W) :
    profiniteQuotientSystemMap G M (f ≫ g) =
      profiniteQuotientSystemMap G M f ≫ profiniteQuotientSystemMap G M g := sorry

/-- The inverse system of finite continuous quotient modules. -/
def profiniteQuotientSystem (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (M : Type u) [AddCommGroup M] [TopologicalSpace M] [DistribMulAction G M]
    [IsTopologicalAddGroup M] [ContinuousSMul G M] : (IsFiniteGaloisQuotient G M).FullSubcategory ⥤
      DiscreteModuleCat ℤ G where
  obj U := finiteQuotientModule G M U
  map f := profiniteQuotientSystemMap G M f
  map_id := profiniteQuotientSystem_map_id G M
  map_comp := profiniteQuotientSystem_map_comp G M

/-- The underlying module of `ofAddGModule` is its original additive group. -/
theorem ofAddGModule_V (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (M : Type u) [AddCommGroup M] [DistribMulAction G M]
    (h : ∀ x : M, IsOpen (MulAction.stabilizer G x : Set G)) :
    (ofAddGModule G M h).obj.V = ModuleCat.of ℤ M := sorry

end ContinuousModule

end
