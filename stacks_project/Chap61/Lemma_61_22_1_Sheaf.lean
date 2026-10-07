module

public import Mathlib.Algebra.Category.Grp.Ulift
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
public import Mathlib.CategoryTheory.IsomorphismClasses
public import Mathlib.CategoryTheory.Sites.Limits
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.CategoryTheory.Sites.Whiskering
public import Mathlib.FieldTheory.KrullTopology
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.RepresentationTheory.Homological.ContCohomology.Basic
public import Mathlib.RepresentationTheory.Homological.ContCohomology.Functoriality
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.Noetherian.Basic
public import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
public import Mathlib.Topology.Algebra.OpenSubgroup
public import stacks_project.Chap59.Definition_59_57_2_TopRep
public import stacks_project.Chap59.Lemma_59_59_1
public import stacks_project.Chap61.Lemma_61_22_1_Comparison

/-!
# Completed Galois sheaves on the small pro-étale site of a point

Given a geometric point of `Spec k`, the étale Galois correspondence supplies
locally constant sheaves on `Spec k_étale`. Pulling back along `ε` and taking
the inverse limit produces the completed Galois sheaf `underline{M}^∧` on
`Spec k_proétale`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite ConcreteCategory
open CategoryTheory.Action.ModuleCat
open AlgebraicGeometry
open AlgebraicGeometry.Scheme.Etale
open ContRepresentation
open scoped ContRepresentation

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.ProEt

/-- The étale sheaf on `Spec k` associated to a discrete continuous
`Gal(k^sep/k)`-module by the inverse of `stalkGaloisModule`. -/
def etaleSheafOfGaloisModule (k : Type u) [Field k]
    (s : GeometricPoint (Spec (.of k))) :
    DiscreteModuleCat ℤ s.absoluteGaloisGroup ⥤
      Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{u} :=
  (stalkGaloisModule k s).asEquivalence.inverse

/-- Recovering the input discrete Galois module as the étale stalk of
`etaleSheafOfGaloisModule`. -/
theorem etaleSheafOfGaloisModule_spec (k : Type u) [Field k]
    (s : GeometricPoint (Spec (.of k)))
    (M : DiscreteModuleCat ℤ s.absoluteGaloisGroup) :
    IsIsomorphic ((stalkGaloisModule k s).obj
      ((etaleSheafOfGaloisModule k s).obj M)) M := sorry

/-- The `I`-adic topology makes `M` a topological additive group. -/
theorem adicModule_isTopologicalAddGroup {Λ : Type u} [CommRing Λ] (I : Ideal Λ)
    (M : Type u) [AddCommGroup M] [Module Λ M] :
    @IsTopologicalAddGroup M (Ideal.adicModuleTopology I M) _ := sorry

/-- Integer scalars act continuously on `M` in the `I`-adic topology. -/
theorem adicModule_continuousSMul_int {Λ : Type u} [CommRing Λ] (I : Ideal Λ)
    (M : Type u) [AddCommGroup M] [Module Λ M] :
    @ContinuousSMul ℤ M _ _ (Ideal.adicModuleTopology I M) := sorry

/-- The submodule `I^n M` is open in the `I`-adic topology. -/
theorem adicQuotient_isOpen {Λ : Type u} [CommRing Λ] (I : Ideal Λ)
    (M : Type u) [AddCommGroup M] [Module Λ M] (n : ℕ) :
    @IsOpen M (Ideal.adicModuleTopology I M)
      ((I ^ n • (⊤ : Submodule Λ M) : Submodule Λ M) : Set M) := sorry

/-- Package a discrete continuous `ℤ[G]`-module from an open-stabilizer witness. -/
def ofAddGModule (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (M : Type u) [AddCommGroup M] [DistribMulAction G M]
    (h : ∀ x : M, IsOpen (MulAction.stabilizer G x : Set G)) :
    DiscreteModuleCat ℤ G :=
  ⟨{ V := ModuleCat.of ℤ M
     ρ :=
       { toFun := fun g ↦
           ModuleCat.ofHom (DistribSMul.toAddMonoidHom M g).toIntLinearMap
         map_one' := sorry
         map_mul' := sorry } }, h⟩

/-- A `G`-equivariant additive map induces a morphism of discrete continuous
modules. -/
def ofAddGModuleMap (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {M N : Type u} [AddCommGroup M] [AddCommGroup N]
    [DistribMulAction G M] [DistribMulAction G N]
    {hM : ∀ x : M, IsOpen (MulAction.stabilizer G x : Set G)}
    {hN : ∀ x : N, IsOpen (MulAction.stabilizer G x : Set G)} (f : M →+ N) :
    ofAddGModule G M hM ⟶ ofAddGModule G N hN :=
  ObjectProperty.homMk
    { hom := ModuleCat.ofHom f.toIntLinearMap
      comm := sorry }

/-- Open finite-index `G`-invariant additive subgroups of a topological
`G`-module, indexing finite discrete continuous quotients. -/
def IsFiniteGaloisQuotient (G : Type u) [Group G]
    (M : Type u) [AddCommGroup M] [TopologicalSpace M] [DistribMulAction G M] :
    ObjectProperty (OpenAddSubgroup M) :=
  fun U ↦ Finite (M ⧸ U.toAddSubgroup) ∧
    ∀ g : G, AddSubgroup.map (DistribSMul.toAddMonoidHom M g) U.toAddSubgroup =
      U.toAddSubgroup

/-- Membership in `IsFiniteGaloisQuotient` is finite index together with
`G`-invariance of the open subgroup. -/
theorem IsFiniteGaloisQuotient.mem_iff (G : Type u) [Group G]
    (M : Type u) [AddCommGroup M] [TopologicalSpace M] [DistribMulAction G M]
    (U : OpenAddSubgroup M) :
    IsFiniteGaloisQuotient G M U ↔
      Finite (M ⧸ U.toAddSubgroup) ∧
        ∀ g : G, AddSubgroup.map (DistribSMul.toAddMonoidHom M g) U.toAddSubgroup =
          U.toAddSubgroup := sorry

/-- The unit open subgroup, as a finite Galois quotient. -/
def finiteGaloisQuotient_top (G : Type u) [Group G]
    (M : Type u) [AddCommGroup M] [TopologicalSpace M] [DistribMulAction G M] :
    (IsFiniteGaloisQuotient G M).FullSubcategory :=
  ⟨⊤, sorry⟩

/-- `G`-invariance of an `I`-adic stage, used to descend the action to
`M ⧸ I^n M`. -/
theorem adicQuotient_mapsTo (G : Type u) [Group G]
    {Λ : Type u} [CommRing Λ] (I : Ideal Λ) (M : Type u)
    [AddCommGroup M] [Module Λ M] [DistribMulAction G M]
    [SMulCommClass G Λ M] (n : ℕ) (g : G) :
    (I ^ n • (⊤ : Submodule Λ M)).toAddSubgroup ≤
      ((I ^ n • (⊤ : Submodule Λ M)).toAddSubgroup.comap
        (DistribSMul.toAddMonoidHom M g)) := sorry

/-- The additive endomorphism of `M ⧸ I^n M` induced by `g`. -/
def adicQuotientSMul (G : Type u) [Group G]
    {Λ : Type u} [CommRing Λ] (I : Ideal Λ) (M : Type u)
    [AddCommGroup M] [Module Λ M] [DistribMulAction G M]
    [SMulCommClass G Λ M] (n : ℕ) (g : G) :
    (M ⧸ (I ^ n • (⊤ : Submodule Λ M))) →+
      (M ⧸ (I ^ n • (⊤ : Submodule Λ M))) :=
  QuotientAddGroup.map
    (I ^ n • (⊤ : Submodule Λ M)).toAddSubgroup
    (I ^ n • (⊤ : Submodule Λ M)).toAddSubgroup
    (DistribSMul.toAddMonoidHom M g)
    (adicQuotient_mapsTo G I M n g)

/-- The `G`-action on an `I`-adic quotient stage. -/
instance adicQuotient_distribMulAction (G : Type u) [Group G]
    {Λ : Type u} [CommRing Λ] (I : Ideal Λ) (M : Type u)
    [AddCommGroup M] [Module Λ M] [DistribMulAction G M]
    [SMulCommClass G Λ M] (n : ℕ) :
    DistribMulAction G (M ⧸ (I ^ n • (⊤ : Submodule Λ M))) where
  smul g x := adicQuotientSMul G I M n g x
  one_smul := sorry
  mul_smul := sorry
  smul_zero := sorry
  smul_add := sorry

/-- Open-stabilizer membership of an `I`-adic quotient, using continuity of the
`G`-action for the `I`-adic topology and openness of `I^n M`. -/
theorem adicQuotient_openStabilizer (G : Type u) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] {Λ : Type u} [CommRing Λ] (I : Ideal Λ) (M : Type u)
    [AddCommGroup M] [Module Λ M] [DistribMulAction G M] [SMulCommClass G Λ M]
    [hcont : @ContinuousSMul G M _ _ (Ideal.adicModuleTopology I M)] (n : ℕ) :
    ∀ x : M ⧸ (I ^ n • (⊤ : Submodule Λ M)),
      IsOpen (MulAction.stabilizer G x : Set G) := sorry

/-- The discrete continuous Galois module `M_n = M ⧸ I^n M`. -/
def adicQuotientModule (k : Type u) [Field k]
    (s : GeometricPoint (Spec (.of k))) {Λ : Type u} [CommRing Λ]
    (I : Ideal Λ) (M : Type u) [AddCommGroup M] [Module Λ M]
    [DistribMulAction s.absoluteGaloisGroup M] [SMulCommClass s.absoluteGaloisGroup Λ M]
    [hcont : @ContinuousSMul s.absoluteGaloisGroup M _ _ (Ideal.adicModuleTopology I M)] (n : ℕ) :
    DiscreteModuleCat ℤ s.absoluteGaloisGroup :=
  ofAddGModule s.absoluteGaloisGroup (M ⧸ (I ^ n • (⊤ : Submodule Λ M)))
    (adicQuotient_openStabilizer s.absoluteGaloisGroup I M n)

/-- Transition maps of the `I`-adic inverse system on kernels. -/
theorem adicQuotient_le {Λ : Type u} [CommRing Λ] (I : Ideal Λ)
    (M : Type u) [AddCommGroup M] [Module Λ M] {n m : ℕ} (h : n ≤ m) :
    (I ^ m • (⊤ : Submodule Λ M)).toAddSubgroup ≤
      (I ^ n • (⊤ : Submodule Λ M)).toAddSubgroup := sorry

/-- The cofiltered inverse system `n ↦ M ⧸ I^n M` of discrete continuous
Galois modules. -/
def adicQuotientSystem (k : Type u) [Field k]
    (s : GeometricPoint (Spec (.of k))) {Λ : Type u} [CommRing Λ]
    (I : Ideal Λ) (M : Type u) [AddCommGroup M] [Module Λ M]
    [DistribMulAction s.absoluteGaloisGroup M] [SMulCommClass s.absoluteGaloisGroup Λ M]
    [hcont : @ContinuousSMul s.absoluteGaloisGroup M _ _ (Ideal.adicModuleTopology I M)] :
    ℕᵒᵖ ⥤ DiscreteModuleCat ℤ s.absoluteGaloisGroup where
  obj n := adicQuotientModule k s I M (unop n)
  map {n m} f :=
    ofAddGModuleMap s.absoluteGaloisGroup
      (QuotientAddGroup.map
        (I ^ (unop n) • (⊤ : Submodule Λ M)).toAddSubgroup
        (I ^ (unop m) • (⊤ : Submodule Λ M)).toAddSubgroup
        (AddMonoidHom.id M)
        (adicQuotient_le I M (leOfHom (unop f))))
  map_id := sorry
  map_comp := sorry

/-- The pulled-back inverse system `n ↦ ε⁻¹ underline{M_n}` on the small
pro-étale site. -/
def completedGaloisSystem (k : Type u) [Field k]
    (s : GeometricPoint (Spec (.of k))) {Λ : Type u} [CommRing Λ]
    (I : Ideal Λ) (M : Type u) [AddCommGroup M] [Module Λ M]
    [DistribMulAction s.absoluteGaloisGroup M] [SMulCommClass s.absoluteGaloisGroup Λ M]
    [hcont : @ContinuousSMul s.absoluteGaloisGroup M _ _ (Ideal.adicModuleTopology I M)] :
    ℕᵒᵖ ⥤ Sheaf (topology (Spec (.of k))) AddCommGrpCat.{u} :=
  adicQuotientSystem k s I M ⋙
    etaleSheafOfGaloisModule k s ⋙ etaleSheafPullback (Spec (.of k))

/-- The completed Galois sheaf `underline{M}^∧ = lim ε⁻¹ underline{M_n}`
attached to an `I`-adically complete Galois module. -/
public def completedGaloisSheaf (k : Type u) [Field k]
    (s : GeometricPoint (Spec (.of k))) {Λ : Type u} [CommRing Λ]
    (I : Ideal Λ) (M : Type u) [AddCommGroup M] [Module Λ M]
    [IsAdicComplete I M]
    [DistribMulAction s.absoluteGaloisGroup M] [SMulCommClass s.absoluteGaloisGroup Λ M]
    [hcont : @ContinuousSMul s.absoluteGaloisGroup M _ _ (Ideal.adicModuleTopology I M)] :
    Sheaf (topology (Spec (.of k))) AddCommGrpCat.{u} :=
  limit (completedGaloisSystem k s I M)

/-- Projection from the completed Galois sheaf onto the `n`th pulled-back
discrete stage. -/
def completedGaloisSheaf_π (k : Type u) [Field k]
    (s : GeometricPoint (Spec (.of k))) {Λ : Type u} [CommRing Λ]
    (I : Ideal Λ) (M : Type u) [AddCommGroup M] [Module Λ M]
    [IsAdicComplete I M]
    [DistribMulAction s.absoluteGaloisGroup M] [SMulCommClass s.absoluteGaloisGroup Λ M]
    [hcont : @ContinuousSMul s.absoluteGaloisGroup M _ _ (Ideal.adicModuleTopology I M)] (n : ℕ) :
    completedGaloisSheaf k s I M ⟶
      (completedGaloisSystem k s I M).obj (op n) :=
  limit.π (completedGaloisSystem k s I M) (op n)

/-- The completed Galois sheaf is a limit of its discrete pulled-back stages. -/
def completedGaloisSheaf_isLimit (k : Type u) [Field k]
    (s : GeometricPoint (Spec (.of k))) {Λ : Type u} [CommRing Λ]
    (I : Ideal Λ) (M : Type u) [AddCommGroup M] [Module Λ M]
    [IsAdicComplete I M]
    [DistribMulAction s.absoluteGaloisGroup M] [SMulCommClass s.absoluteGaloisGroup Λ M]
    [hcont : @ContinuousSMul s.absoluteGaloisGroup M _ _ (Ideal.adicModuleTopology I M)] :
    IsLimit (limit.cone (completedGaloisSystem k s I M)) :=
  limit.isLimit (completedGaloisSystem k s I M)

/-- Scalar multiplication by `λ` on an adic quotient, as a `G`-module map. -/
def adicQuotientModule_smul (k : Type u) [Field k]
    (s : GeometricPoint (Spec (.of k))) {Λ : Type u} [CommRing Λ]
    (I : Ideal Λ) (M : Type u) [AddCommGroup M] [Module Λ M]
    [DistribMulAction s.absoluteGaloisGroup M] [SMulCommClass s.absoluteGaloisGroup Λ M]
    [hcont : @ContinuousSMul s.absoluteGaloisGroup M _ _ (Ideal.adicModuleTopology I M)] (r : Λ) (n : ℕ) :
    adicQuotientModule k s I M n ⟶ adicQuotientModule k s I M n :=
  ofAddGModuleMap s.absoluteGaloisGroup
    (DistribSMul.toAddMonoidHom (M ⧸ (I ^ n • (⊤ : Submodule Λ M))) r)

/-- Naturality of scalar multiplication on the adic inverse system. -/
def adicQuotientSystem_smul (k : Type u) [Field k]
    (s : GeometricPoint (Spec (.of k))) {Λ : Type u} [CommRing Λ]
    (I : Ideal Λ) (M : Type u) [AddCommGroup M] [Module Λ M]
    [DistribMulAction s.absoluteGaloisGroup M] [SMulCommClass s.absoluteGaloisGroup Λ M]
    [hcont : @ContinuousSMul s.absoluteGaloisGroup M _ _ (Ideal.adicModuleTopology I M)] (r : Λ) :
    adicQuotientSystem k s I M ⟶ adicQuotientSystem k s I M where
  app n := adicQuotientModule_smul k s I M r (unop n)
  naturality := sorry

/-- The sheaf endomorphism of `completedGaloisSheaf` induced by `G`-equivariant
scalar multiplication by `λ`. -/
public def completedGaloisSheaf_smul (k : Type u) [Field k]
    (s : GeometricPoint (Spec (.of k))) {Λ : Type u} [CommRing Λ]
    (I : Ideal Λ) (M : Type u) [AddCommGroup M] [Module Λ M]
    [IsAdicComplete I M]
    [DistribMulAction s.absoluteGaloisGroup M] [SMulCommClass s.absoluteGaloisGroup Λ M]
    [hcont : @ContinuousSMul s.absoluteGaloisGroup M _ _ (Ideal.adicModuleTopology I M)] (r : Λ) :
    completedGaloisSheaf k s I M ⟶ completedGaloisSheaf k s I M :=
  limMap
    (Functor.whiskerRight (adicQuotientSystem_smul k s I M r)
      (etaleSheafOfGaloisModule k s ⋙ etaleSheafPullback (Spec (.of k))))

/-- `G`-invariance of a finite Galois quotient subgroup. -/
theorem finiteGaloisQuotient_mapsTo (G : Type u) [Group G]
    (M : Type u) [AddCommGroup M] [TopologicalSpace M] [DistribMulAction G M]
    (U : (IsFiniteGaloisQuotient G M).FullSubcategory) (g : G) :
    U.obj.toAddSubgroup ≤
      U.obj.toAddSubgroup.comap (DistribSMul.toAddMonoidHom M g) := sorry

/-- The `G`-action on a finite discrete quotient `M ⧸ U`. -/
instance finiteQuotient_distribMulAction (G : Type u) [Group G]
    (M : Type u) [AddCommGroup M] [TopologicalSpace M] [DistribMulAction G M]
    (U : (IsFiniteGaloisQuotient G M).FullSubcategory) :
    DistribMulAction G (M ⧸ U.obj.toAddSubgroup) where
  smul g x :=
    (QuotientAddGroup.map U.obj.toAddSubgroup U.obj.toAddSubgroup
      (DistribSMul.toAddMonoidHom M g) (finiteGaloisQuotient_mapsTo G M U g)) x
  one_smul := sorry
  mul_smul := sorry
  smul_zero := sorry
  smul_add := sorry

/-- Open-stabilizer membership of a finite discrete quotient, using continuity
of the `G`-action and openness of the kernel. -/
theorem finiteQuotient_openStabilizer (G : Type u) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (M : Type u) [AddCommGroup M] [TopologicalSpace M]
    [DistribMulAction G M] [ContinuousSMul G M]
    (U : (IsFiniteGaloisQuotient G M).FullSubcategory) :
    ∀ x : M ⧸ U.obj.toAddSubgroup, IsOpen (MulAction.stabilizer G x : Set G) :=
  sorry

/-- The discrete continuous Galois module `M ⧸ U` attached to a finite
`G`-invariant open subgroup. -/
def finiteQuotientModule (G : Type u) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (M : Type u) [AddCommGroup M] [TopologicalSpace M]
    [DistribMulAction G M] [ContinuousSMul G M]
    (U : (IsFiniteGaloisQuotient G M).FullSubcategory) :
    DiscreteModuleCat ℤ G :=
  ofAddGModule G (M ⧸ U.obj.toAddSubgroup) (finiteQuotient_openStabilizer G M U)

/-- Inclusion of finite Galois quotients induces a map of discrete modules. -/
theorem finiteGaloisQuotient_le (G : Type u) [Group G]
    (M : Type u) [AddCommGroup M] [TopologicalSpace M] [DistribMulAction G M]
    {U V : (IsFiniteGaloisQuotient G M).FullSubcategory} (f : U ⟶ V) :
    U.obj.toAddSubgroup ≤ V.obj.toAddSubgroup := sorry

/-- The inverse system of finite discrete continuous Galois quotients of a
profinite abelian `G`-module. -/
def profiniteQuotientSystem (G : Type u) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (M : Type u) [AddCommGroup M] [TopologicalSpace M]
    [DistribMulAction G M] [ContinuousSMul G M] :
    (IsFiniteGaloisQuotient G M).FullSubcategory ⥤ DiscreteModuleCat ℤ G where
  obj U := finiteQuotientModule G M U
  map {U V} f :=
    ofAddGModuleMap G
      (QuotientAddGroup.map U.obj.toAddSubgroup V.obj.toAddSubgroup
        (AddMonoidHom.id M) (finiteGaloisQuotient_le G M f))
  map_id := sorry
  map_comp := sorry

/-- The pulled-back inverse system of finite Galois quotients on
`Spec k_proétale`. -/
def profiniteGaloisSystem (k : Type u) [Field k]
    (s : GeometricPoint (Spec (.of k))) (M : Type u)
    [AddCommGroup M] [TopologicalSpace M]
    [DistribMulAction s.absoluteGaloisGroup M]
    [ContinuousSMul s.absoluteGaloisGroup M] :
    (IsFiniteGaloisQuotient s.absoluteGaloisGroup M).FullSubcategory ⥤
      Sheaf (topology (Spec (.of k))) AddCommGrpCat.{u} :=
  profiniteQuotientSystem s.absoluteGaloisGroup M ⋙
    etaleSheafOfGaloisModule k s ⋙ etaleSheafPullback (Spec (.of k))

/-- The completed Galois sheaf `underline{M}^∧` attached to a profinite abelian
continuous Galois module, as the inverse limit of finite discrete stages. -/
public def profiniteGaloisSheaf (k : Type u) [Field k]
    (s : GeometricPoint (Spec (.of k))) (M : Type u)
    [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
    [CompactSpace M] [T2Space M] [TotallyDisconnectedSpace M]
    [DistribMulAction s.absoluteGaloisGroup M]
    [ContinuousSMul s.absoluteGaloisGroup M] :
    Sheaf (topology (Spec (.of k))) AddCommGrpCat.{u} :=
  limit (profiniteGaloisSystem k s M)

/-- Projection from the profinite Galois sheaf onto a finite discrete stage. -/
def profiniteGaloisSheaf_π (k : Type u) [Field k]
    (s : GeometricPoint (Spec (.of k))) (M : Type u)
    [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
    [CompactSpace M] [T2Space M] [TotallyDisconnectedSpace M]
    [DistribMulAction s.absoluteGaloisGroup M]
    [ContinuousSMul s.absoluteGaloisGroup M]
    (U : (IsFiniteGaloisQuotient s.absoluteGaloisGroup M).FullSubcategory) :
    profiniteGaloisSheaf k s M ⟶ (profiniteGaloisSystem k s M).obj U :=
  limit.π (profiniteGaloisSystem k s M) U

/-- The topological representation associated to a profinite abelian continuous
Galois module. -/
public def profiniteGaloisTopRep (k : Type u) [Field k]
    (s : GeometricPoint (Spec (.of k))) (M : Type u)
    [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
    [CompactSpace M] [T2Space M] [TotallyDisconnectedSpace M]
    [DistribMulAction s.absoluteGaloisGroup M]
    [ContinuousSMul s.absoluteGaloisGroup M] :
    TopRep ℤ s.absoluteGaloisGroup :=
  TopRep.of
    { toMonoidHom :=
        { toFun := fun g ↦
            { toLinearMap := (DistribSMul.toAddMonoidHom M g).toIntLinearMap
              cont := continuous_const_smul g }
          map_one' := sorry
          map_mul' := sorry } }

/-- The `I`-adic continuous `ℤ`-linear action of `g` on `M`. -/
public def adicGaloisCLM (G : Type u) [Group G] [TopologicalSpace G]
    {Λ : Type u} [CommRing Λ] (I : Ideal Λ) (M : Type u)
    [AddCommGroup M] [Module Λ M] [DistribMulAction G M]
    [hcont : @ContinuousSMul G M _ _ (Ideal.adicModuleTopology I M)] (g : G) :
    @ContinuousLinearMap ℤ ℤ _ _ (RingHom.id ℤ) M (Ideal.adicModuleTopology I M) _ M
      (Ideal.adicModuleTopology I M) _ _ _ :=
  @ContinuousLinearMap.mk ℤ ℤ _ _ (RingHom.id ℤ) M (Ideal.adicModuleTopology I M) _ M
    (Ideal.adicModuleTopology I M) _ _ _
    (DistribSMul.toAddMonoidHom M g).toIntLinearMap sorry

/-- The `I`-adic continuous representation of `G` on `M`. -/
public def completedGaloisContRepresentation (G : Type u) [Group G] [TopologicalSpace G]
    {Λ : Type u} [CommRing Λ] (I : Ideal Λ) (M : Type u)
    [AddCommGroup M] [Module Λ M] [DistribMulAction G M]
    [hcont : @ContinuousSMul G M _ _ (Ideal.adicModuleTopology I M)] :
    @ContRepresentation ℤ G M _ _ _ (Ideal.adicModuleTopology I M)
      (adicModule_isTopologicalAddGroup I M) _ :=
  @ContRepresentation.ofMonoidHom ℤ G M _ _ _ (Ideal.adicModuleTopology I M)
    (adicModule_isTopologicalAddGroup I M) _
    { toFun := fun g ↦ adicGaloisCLM G I M g
      map_one' := sorry
      map_mul' := sorry }

/-- The topological representation associated to an `I`-adically complete
Galois module, with the `I`-adic topology on `M`. -/
public def completedGaloisTopRep (k : Type u) [Field k]
    (s : GeometricPoint (Spec (.of k))) {Λ : Type u} [CommRing Λ]
    (I : Ideal Λ) (M : Type u) [AddCommGroup M] [Module Λ M]
    [IsAdicComplete I M] [DistribMulAction s.absoluteGaloisGroup M]
    [SMulCommClass s.absoluteGaloisGroup Λ M]
    [hcont : @ContinuousSMul s.absoluteGaloisGroup M _ _ (Ideal.adicModuleTopology I M)] :
    TopRep ℤ s.absoluteGaloisGroup :=
  @TopRep.of ℤ s.absoluteGaloisGroup M _ _ _ _ _ (Ideal.adicModuleTopology I M)
    (adicModule_isTopologicalAddGroup I M) (adicModule_continuousSMul_int I M)
    (completedGaloisContRepresentation s.absoluteGaloisGroup I M)

/-- Grothendieck-abelian structure on abelian sheaves on the small pro-étale
site after the `u ↦ u+1` ulift, matching `ellAdicSheaf`. -/
instance isGrothendieckAbelian_sheaf_proEt (S : Scheme.{u}) :
    IsGrothendieckAbelian.{u + 1}
      (Sheaf (topology S) AddCommGrpCat.{u + 1}) :=
  have : EssentiallySmall.{u + 1} S.ProEt := inferInstance
  Sheaf.isGrothendieckAbelian_of_essentiallySmall (topology S) AddCommGrpCat.{u + 1}

/-- Pro-étale cohomology of an abelian sheaf on the small pro-étale site,
after the ulift used by `EllAdicCohomology`. -/
public def proEtaleCohomology (S : Scheme.{u})
    (F : Sheaf (topology S) AddCommGrpCat.{u}) (n : ℕ) : AddCommGrpCat.{u + 1} :=
  AddCommGrpCat.of
    (((sheafCompose (topology S) AddCommGrpCat.uliftFunctor.{u + 1, u}).obj F).H n)

/-- Tate continuous cohomology, ulifted to the same universe as
`proEtaleCohomology`. -/
public def continuousCohomologyAb (G : Type u) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (A : TopRep ℤ G) (n : ℕ) : AddCommGrpCat.{u + 1} :=
  AddCommGrpCat.uliftFunctor.{u + 1, u}.obj
    (AddCommGrpCat.of (continuousCohomology n A : Type u))

/-- The underlying `ℤ`-module of `ofAddGModule` is the original additive group. -/
theorem ofAddGModule_V (G : Type u) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (M : Type u) [AddCommGroup M] [DistribMulAction G M]
    (h : ∀ x : M, IsOpen (MulAction.stabilizer G x : Set G)) :
    (ofAddGModule G M h).obj.V = ModuleCat.of ℤ M := sorry

/-- The underlying carrier of `profiniteGaloisTopRep` is the original module. -/
theorem profiniteGaloisTopRep_V (k : Type u) [Field k]
    (s : GeometricPoint (Spec (.of k))) (M : Type u)
    [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
    [CompactSpace M] [T2Space M] [TotallyDisconnectedSpace M]
    [DistribMulAction s.absoluteGaloisGroup M]
    [ContinuousSMul s.absoluteGaloisGroup M] :
    (profiniteGaloisTopRep k s M).V = M := sorry

/-- The underlying carrier of `completedGaloisTopRep` is the original module. -/
theorem completedGaloisTopRep_V (k : Type u) [Field k]
    (s : GeometricPoint (Spec (.of k))) {Λ : Type u} [CommRing Λ]
    (I : Ideal Λ) (M : Type u) [AddCommGroup M] [Module Λ M]
    [IsAdicComplete I M] [DistribMulAction s.absoluteGaloisGroup M]
    [SMulCommClass s.absoluteGaloisGroup Λ M]
    [hcont : @ContinuousSMul s.absoluteGaloisGroup M _ _ (Ideal.adicModuleTopology I M)] :
    (completedGaloisTopRep k s I M).V = M := sorry

/-- The map on pro-étale cohomology induced by a morphism of abelian sheaves. -/
public def proEtaleCohomologyMap {S : Scheme.{u}}
    {F G : Sheaf (topology S) AddCommGrpCat.{u}} (f : F ⟶ G) (n : ℕ) :
    proEtaleCohomology S F n ⟶ proEtaleCohomology S G n :=
  AddCommGrpCat.ofHom
    (Sheaf.H.map
      ((sheafCompose (topology S) AddCommGrpCat.uliftFunctor.{u + 1, u}).map f) n)

/-- Scalar multiplication by `1` acts as the identity on `completedGaloisSheaf`. -/
theorem completedGaloisSheaf_smul_one
    (k : Type u) [Field k] (s : GeometricPoint (Spec (.of k)))
    (Λ : Type u) [CommRing Λ] (I : Ideal Λ)
    (M : Type u) [AddCommGroup M] [Module Λ M] [IsAdicComplete I M]
    [DistribMulAction s.absoluteGaloisGroup M]
    [SMulCommClass s.absoluteGaloisGroup Λ M]
    [hcont : @ContinuousSMul s.absoluteGaloisGroup M _ _ (Ideal.adicModuleTopology I M)] :
    completedGaloisSheaf_smul k s I M 1 = 𝟙 (completedGaloisSheaf k s I M) :=
  sorry

/-- Addition of scalars is addition of sheaf endomorphisms of
`completedGaloisSheaf`. -/
theorem completedGaloisSheaf_smul_add
    (k : Type u) [Field k] (s : GeometricPoint (Spec (.of k)))
    (Λ : Type u) [CommRing Λ] (I : Ideal Λ)
    (M : Type u) [AddCommGroup M] [Module Λ M] [IsAdicComplete I M]
    [DistribMulAction s.absoluteGaloisGroup M]
    [SMulCommClass s.absoluteGaloisGroup Λ M]
    [hcont : @ContinuousSMul s.absoluteGaloisGroup M _ _ (Ideal.adicModuleTopology I M)] (r t : Λ) :
    completedGaloisSheaf_smul k s I M (r + t) =
      completedGaloisSheaf_smul k s I M r +
        completedGaloisSheaf_smul k s I M t :=
  sorry

/-- Multiplication of scalars is composition of sheaf endomorphisms of
`completedGaloisSheaf`. -/
theorem completedGaloisSheaf_smul_mul
    (k : Type u) [Field k] (s : GeometricPoint (Spec (.of k)))
    (Λ : Type u) [CommRing Λ] (I : Ideal Λ)
    (M : Type u) [AddCommGroup M] [Module Λ M] [IsAdicComplete I M]
    [DistribMulAction s.absoluteGaloisGroup M]
    [SMulCommClass s.absoluteGaloisGroup Λ M]
    [hcont : @ContinuousSMul s.absoluteGaloisGroup M _ _ (Ideal.adicModuleTopology I M)] (r t : Λ) :
    completedGaloisSheaf_smul k s I M (r * t) =
      completedGaloisSheaf_smul k s I M t ≫
        completedGaloisSheaf_smul k s I M r :=
  sorry

/-- The `Λ`-module structure on pro-étale cohomology of `completedGaloisSheaf`,
induced by `completedGaloisSheaf_smul`. -/
public instance module_proEtaleCohomology_completedGaloisSheaf
    (k : Type u) [Field k] (s : GeometricPoint (Spec (.of k)))
    (Λ : Type u) [CommRing Λ] (I : Ideal Λ)
    (M : Type u) [AddCommGroup M] [Module Λ M] [IsAdicComplete I M]
    [DistribMulAction s.absoluteGaloisGroup M]
    [SMulCommClass s.absoluteGaloisGroup Λ M]
    [hcont : @ContinuousSMul s.absoluteGaloisGroup M _ _ (Ideal.adicModuleTopology I M)] (i : ℕ) :
    Module Λ (proEtaleCohomology (Spec (.of k)) (completedGaloisSheaf k s I M) i) where
  smul r x := proEtaleCohomologyMap (completedGaloisSheaf_smul k s I M r) i x
  one_smul := sorry
  mul_smul := sorry
  smul_zero := sorry
  smul_add := sorry
  add_smul := sorry
  zero_smul := sorry

/-- The `I`-adic continuous `ℤ`-linear endomorphism of `M` given by scalar
multiplication by `r`. -/
def adicScalarCLM {Λ : Type u} [CommRing Λ] (I : Ideal Λ) (M : Type u)
    [AddCommGroup M] [Module Λ M] (r : Λ) :
    @ContinuousLinearMap ℤ ℤ _ _ (RingHom.id ℤ) M (Ideal.adicModuleTopology I M) _ M
      (Ideal.adicModuleTopology I M) _ _ _ :=
  @ContinuousLinearMap.mk ℤ ℤ _ _ (RingHom.id ℤ) M (Ideal.adicModuleTopology I M) _ M
    (Ideal.adicModuleTopology I M) _ _ _
    (DistribSMul.toAddMonoidHom M r).toIntLinearMap sorry

/-- The endomorphism of `completedGaloisTopRep` induced by scalar multiplication
by `r`. -/
public def completedGaloisTopRep_smul
    (k : Type u) [Field k] (s : GeometricPoint (Spec (.of k)))
    {Λ : Type u} [CommRing Λ] (I : Ideal Λ)
    (M : Type u) [AddCommGroup M] [Module Λ M] [IsAdicComplete I M]
    [DistribMulAction s.absoluteGaloisGroup M]
    [SMulCommClass s.absoluteGaloisGroup Λ M]
    [hcont : @ContinuousSMul s.absoluteGaloisGroup M _ _ (Ideal.adicModuleTopology I M)] (r : Λ) :
    completedGaloisTopRep k s I M ⟶ completedGaloisTopRep k s I M :=
  ConcreteCategory.ofHom
    ({ toLinearMap := (DistribSMul.toAddMonoidHom M r).toIntLinearMap
       cont := sorry
       isIntertwining' := sorry } :
      (completedGaloisTopRep k s I M).ρ →ⁱL (completedGaloisTopRep k s I M).ρ)

/-- The map on ulifted continuous cohomology induced by a morphism of topological
representations. -/
public def continuousCohomologyAbMap {G : Type u} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] {A B : TopRep ℤ G} (f : A ⟶ B) (n : ℕ) :
    continuousCohomologyAb G A n ⟶ continuousCohomologyAb G B n :=
  AddCommGrpCat.uliftFunctor.{u + 1, u}.map
    (AddCommGrpCat.ofHom
      ((ContinuousCohomology.map (ContinuousMonoidHom.id G) f n).hom.toLinearMap.toAddMonoidHom))

/-- The `Λ`-module structure on continuous cohomology of `completedGaloisTopRep`,
induced by the `Λ`-action on `M`. -/
public instance module_continuousCohomologyAb_completedGalois
    (k : Type u) [Field k] (s : GeometricPoint (Spec (.of k)))
    (Λ : Type u) [CommRing Λ] (I : Ideal Λ)
    (M : Type u) [AddCommGroup M] [Module Λ M] [IsAdicComplete I M]
    [DistribMulAction s.absoluteGaloisGroup M]
    [SMulCommClass s.absoluteGaloisGroup Λ M]
    [hcont : @ContinuousSMul s.absoluteGaloisGroup M _ _ (Ideal.adicModuleTopology I M)] (i : ℕ) :
    Module Λ
      (continuousCohomologyAb s.absoluteGaloisGroup
        (completedGaloisTopRep k s I M) i) where
  smul r x :=
    continuousCohomologyAbMap (completedGaloisTopRep_smul k s I M r) i x
  one_smul := sorry
  mul_smul := sorry
  smul_zero := sorry
  smul_add := sorry
  add_smul := sorry
  zero_smul := sorry

end AlgebraicGeometry.Scheme.ProEt

