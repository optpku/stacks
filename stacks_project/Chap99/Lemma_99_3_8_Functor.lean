/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
public import Mathlib.Algebra.Homology.ShortComplex.Homology
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
public import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects
public import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLTGE
public import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLEGT
public import ReasLib.CategoryTheory.DerivedCategory.Concentrated.Basic
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Unbounded.LeftDerived.Bounds
public import ReasLib.CategoryTheory.DerivedCategory.Truncation.Homology
public import stacks_project.Chap66.«66_26_0_1_Pushforward»
public import stacks_project.Chap69.Lemma_69_11_2_Flat_base_change_BaseChange
public import stacks_project.Chap69.Lemma_69_20_4_Pullback
public import stacks_project.Chap75.Definition_75_14_1_PerfectApproximation
public import stacks_project.Chap75.Lemma_75_13_6_PseudoCoherent
public import stacks_project.Chap75.Lemma_75_26_4_VectorBundle
public import stacks_project.Chap75.Lemma_75_26_6_Pullback
public import stacks_project.Chap75.Lemma_75_26_6_RankLocus
public import stacks_project.Chap75.Lemma_75_26_7_StructureSheaf
public import stacks_project.Chap99.Lemma_99_3_8_Yoneda

/-!
# Degree-zero section functors of a derived module on `B`

A pseudo-coherent derived `𝒪_B`-module `K` determines two functors on
`(Sch/B)ᵒᵖ`: global sections of `H^0(Lg^* K)`, and derived Hom from `𝒪_T[0]`
into `Lg^* K`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace AlgebraicGeometry.AlgebraicSpace.Modules
open DerivedCategory.TStructure Opposite ComplexShape

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.ModuleDerived

variable {S : Scheme.{u}} {B : AlgebraicSpace S}

/-- Derived pullback of `K` along the structural morphism of a scheme over `B`. -/
abbrev pullbackOver (K : ModuleDerived B) (σ : SchemeOver B) :
    ModuleDerived (ofOver σ.left) :=
  (pullback σ.hom).obj K

/-- `pullbackOver K σ` is unbounded derived pullback of `K` along `σ.hom`. -/
theorem pullbackOver_eq (K : ModuleDerived B) (σ : SchemeOver B) :
    pullbackOver K σ = (pullback σ.hom).obj K :=
  rfl

/-- Module pullback along a morphism of algebraic spaces is a left adjoint. -/
instance instIsLeftAdjoint_modulesPullback {Y X : AlgebraicSpace S} (f : Y ⟶ X) :
    (Modules.pullback f).IsLeftAdjoint :=
  (Modules.pullbackPushforwardAdjunction f).isLeftAdjoint

/-- Ordinary pullback of cohomology compared with cohomology of termwise pullback of a
representative cochain complex. -/
def modulesPullbackHomologyComparison {Y X : AlgebraicSpace S} (f : Y ⟶ X)
    (K : CochainComplex (Modules X) ℤ) (i : ℤ) :
    (Modules.pullback f).obj (K.homology i) ⟶
      (((Modules.pullback f).mapHomologicalComplex (up ℤ)).obj K).homology i :=
  let F := Modules.pullback f
  let scK := K.sc i
  let lift := kernel.lift scK.g scK.f scK.zero
  let liftF :=
    kernel.lift (F.map scK.g) (F.map scK.f)
      ((F.map_comp scK.f scK.g).symm.trans
        ((congrArg F.map scK.zero).trans (F.map_zero scK.X₁ scK.X₃)))
  F.map (ShortComplex.homologyIsoCokernelLift scK).hom ≫
    (PreservesCokernel.iso F lift).hom ≫
      cokernel.map (F.map lift) liftF (𝟙 (F.obj scK.X₁)) (kernelComparison scK.g F)
        ((map_lift_kernelComparison (f := scK.g) (G := F) (h := scK.f) scK.zero).trans
          (Category.id_comp liftF).symm) ≫
        (ShortComplex.homologyIsoCokernelLift
          ((((Modules.pullback f).mapHomologicalComplex (up ℤ)).obj K).sc i)).inv

/-- `modulesPullbackHomologyComparison` is ordinary pullback of homology followed by the
cokernel comparison of module pullback and the homology identification of the pulled-back
short complex. -/
theorem modulesPullbackHomologyComparison_eq {Y X : AlgebraicSpace S} (f : Y ⟶ X)
    (K : CochainComplex (Modules X) ℤ) (i : ℤ) :
    modulesPullbackHomologyComparison f K i =
      let F := Modules.pullback f
      let scK := K.sc i
      let lift := kernel.lift scK.g scK.f scK.zero
      let liftF :=
        kernel.lift (F.map scK.g) (F.map scK.f)
          ((F.map_comp scK.f scK.g).symm.trans
            ((congrArg F.map scK.zero).trans (F.map_zero scK.X₁ scK.X₃)))
      F.map (ShortComplex.homologyIsoCokernelLift scK).hom ≫
        (PreservesCokernel.iso F lift).hom ≫
          cokernel.map (F.map lift) liftF (𝟙 (F.obj scK.X₁)) (kernelComparison scK.g F)
            ((map_lift_kernelComparison (f := scK.g) (G := F) (h := scK.f) scK.zero).trans
              (Category.id_comp liftF).symm) ≫
            (ShortComplex.homologyIsoCokernelLift
              ((((Modules.pullback f).mapHomologicalComplex (up ℤ)).obj K).sc i)).inv :=
  rfl

/-- Derived pullback of modules is the total left derived functor of underived
module pullback. -/
instance instIsLeftDerivedFunctor_pullback {Y X : AlgebraicSpace S} (f : Y ⟶ X) :
    (pullback f).IsLeftDerivedFunctor
      (Functor.LeftDerived.Homotopy.counit (Modules.pullback f))
      (HomotopyCategory.quasiIso (Modules X) (up ℤ)) :=
  Functor.LeftDerived.Homotopy.isLeftDerived (Modules.pullback f)

/-- The lower truncation `τ_{≥ i} E` of an object bounded above by `i` is identified
with the degree-`i` cohomology sheaf placed in degree `i`. Both directions are
library maps. -/
def truncGESingleIso {X : AlgebraicSpace S} (E : ModuleDerived X) (i : ℤ)
    [E.IsLE i] :
    (t.truncGE i).obj E ≅
      (DerivedCategory.singleFunctor (Modules X) i).obj (cohomologySheaf E i) :=
  DerivedCategory.Concentrated.singleIsoOfBounds (Modules X) ((t.truncGE i).obj E) i ≪≫
    (DerivedCategory.singleFunctor (Modules X) i).mapIso
      (DerivedCategory.TruncGE.homologyIso E i i le_rfl)

/-- The hom of `truncGESingleIso` is `singleIsoOfBounds` followed by `singleFunctor`
of the lower-truncation homology identification. -/
theorem truncGESingleIso_hom {X : AlgebraicSpace S} (E : ModuleDerived X) (i : ℤ)
    [E.IsLE i] :
    (truncGESingleIso E i).hom =
      (DerivedCategory.Concentrated.singleIsoOfBounds (Modules X) ((t.truncGE i).obj E) i).hom ≫
        (DerivedCategory.singleFunctor (Modules X) i).map
          (DerivedCategory.TruncGE.homologyIso E i i le_rfl).hom :=
  rfl

/-- The inv of `truncGESingleIso` is `singleFunctor` of the inverse lower-truncation
homology identification followed by the inverse of `singleIsoOfBounds`. -/
theorem truncGESingleIso_inv {X : AlgebraicSpace S} (E : ModuleDerived X) (i : ℤ)
    [E.IsLE i] :
    (truncGESingleIso E i).inv =
      (DerivedCategory.singleFunctor (Modules X) i).map
          (DerivedCategory.TruncGE.homologyIso E i i le_rfl).inv ≫
        (DerivedCategory.Concentrated.singleIsoOfBounds (Modules X) ((t.truncGE i).obj E) i).inv :=
  rfl

/-- A derived module bounded above by `i` maps canonically to its degree-`i` cohomology sheaf
placed in degree `i`, by lower truncation followed by `truncGESingleIso`. -/
def upperCohomologyProjection {X : AlgebraicSpace S} (E : ModuleDerived X) (i : ℤ)
    [E.IsLE i] :
    E ⟶ (DerivedCategory.singleFunctor (Modules X) i).obj (cohomologySheaf E i) :=
  (t.truncGEπ i).app E ≫ (truncGESingleIso E i).hom

/-- `upperCohomologyProjection` is the lower-truncation projection followed by
`truncGESingleIso`. -/
theorem upperCohomologyProjection_eq {X : AlgebraicSpace S} (E : ModuleDerived X) (i : ℤ)
    [E.IsLE i] :
    upperCohomologyProjection E i =
      (t.truncGEπ i).app E ≫ (truncGESingleIso E i).hom :=
  rfl

/-- The unbounded comparison `f^* H^i(E) ⟶ H^i(Lf^* E)`. It is ordinary pullback of
`TruncGE.homologyIso.inv`, the lower-edge comparison on `τ_{≥ i} E`, and the inverse
left-derived lower-truncation homology identification. -/
def cohomologySheafPullbackComparison {Y X : AlgebraicSpace S} (f : Y ⟶ X)
    (E : ModuleDerived X) (i : ℤ) :
    (Modules.pullback f).obj (cohomologySheaf E i) ⟶
      cohomologySheaf ((pullback f).obj E) i :=
  (Modules.pullback f).map (DerivedCategory.TruncGE.homologyIso E i i le_rfl).inv ≫
    cohomologyPullbackComparison f ((t.truncGE i).obj E) i inferInstance inferInstance ≫
      (Functor.LeftDerived.Homotopy.TruncGE.homologyIso
        (Modules.pullback f) (pullback f)
        (Functor.LeftDerived.Homotopy.counit (Modules.pullback f))
        E i i le_rfl).inv

/-- `cohomologySheafPullbackComparison` is ordinary pullback of `TruncGE.homologyIso.inv`,
the lower-edge comparison on `τ_{≥ i} E`, and the inverse left-derived lower-truncation
homology identification. -/
theorem cohomologySheafPullbackComparison_eq {Y X : AlgebraicSpace S} (f : Y ⟶ X)
    (E : ModuleDerived X) (i : ℤ) :
    cohomologySheafPullbackComparison f E i =
      (Modules.pullback f).map (DerivedCategory.TruncGE.homologyIso E i i le_rfl).inv ≫
        cohomologyPullbackComparison f ((t.truncGE i).obj E) i inferInstance inferInstance ≫
          (Functor.LeftDerived.Homotopy.TruncGE.homologyIso
            (Modules.pullback f) (pullback f)
            (Functor.LeftDerived.Homotopy.counit (Modules.pullback f))
            E i i le_rfl).inv :=
  rfl

/-- Restriction of `H^0(Lg^* K)`-sections along a morphism of schemes over `B`. -/
def cohomologyZeroRestrict (K : ModuleDerived B) {σ τ : SchemeOver B} (h : τ ⟶ σ)
    (ψ : SheafOfModules.unit (structureSheaf (ofOver σ.left)) ⟶
      cohomologySheaf (pullbackOver K σ) 0) :
    SheafOfModules.unit (structureSheaf (ofOver τ.left)) ⟶
      cohomologySheaf (pullbackOver K τ) 0 :=
  structureModulePullbackInv ((ofOverFunctor S).map h.left) ≫
    (Modules.pullback ((ofOverFunctor S).map h.left)).map ψ ≫
      cohomologySheafPullbackComparison ((ofOverFunctor S).map h.left)
          (pullbackOver K σ) 0 ≫
        (DerivedCategory.homologyFunctor (Modules (ofOver τ.left)) 0).map
          ((pullbackCompComparison ((ofOverFunctor S).map h.left) σ.hom).app K) ≫
          eqToHom
            (congrArg (fun k ↦ cohomologySheaf ((pullback k).obj K) 0)
              (CostructuredArrow.w h))

/-- Derived pullback of the structure sheaf in degree `0` recovers the structure sheaf of
the source, with both directions given as data. -/
def structureSheafDerivedPullbackIso {Y X : AlgebraicSpace S} (f : Y ⟶ X) :
    structureSheafDerived Y ≅
      (DerivedCategory.singleFunctor (Modules Y) 0).obj
        ((Modules.pullback f).obj (SheafOfModules.unit (structureSheaf X))) where
  hom := (DerivedCategory.singleFunctor (Modules Y) 0).map (structureModulePullbackInv f)
  inv := (DerivedCategory.singleFunctor (Modules Y) 0).map (IdealSubobject.pullbackUnit f)
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The hom of `structureSheafDerivedPullbackIso` is `singleFunctor` of
`structureModulePullbackInv`. -/
theorem structureSheafDerivedPullbackIso_hom {Y X : AlgebraicSpace S} (f : Y ⟶ X) :
    (structureSheafDerivedPullbackIso f).hom =
      (DerivedCategory.singleFunctor (Modules Y) 0).map (structureModulePullbackInv f) :=
  rfl

/-- The inv of `structureSheafDerivedPullbackIso` is `singleFunctor` of
`IdealSubobject.pullbackUnit`. -/
theorem structureSheafDerivedPullbackIso_inv {Y X : AlgebraicSpace S} (f : Y ⟶ X) :
    (structureSheafDerivedPullbackIso f).inv =
      (DerivedCategory.singleFunctor (Modules Y) 0).map (IdealSubobject.pullbackUnit f) :=
  rfl

/-- The reverse comparison `Lf^* 𝒪_X[0] ⟶ 𝒪_Y[0]` of derived pullback of the structure sheaf. -/
def structureSheafDerivedPullbackCounit {Y X : AlgebraicSpace S} (f : Y ⟶ X) :
    (pullback f).obj (structureSheafDerived X) ⟶ structureSheafDerived Y :=
  singlePullbackComparison f (SheafOfModules.unit (structureSheaf X)) 0 ≫
    (structureSheafDerivedPullbackIso f).inv

/-- Derived pullback of the structure sheaf in degree zero is bounded below by zero. -/
instance instIsGE_pullback_structureSheafDerived {Y X : AlgebraicSpace S} (f : Y ⟶ X) :
    ((pullback f).obj (structureSheafDerived X)).IsGE 0 :=
  sorry

/-- The canonical unit `𝒪_Y[0] ⟶ Lf^* 𝒪_X[0]`, from the underived structure-sheaf unit,
the existing single-sheaf homology comparison, and `lowerCohomologyInclusion`. -/
def structureSheafDerivedPullbackUnit {Y X : AlgebraicSpace S} (f : Y ⟶ X) :
    structureSheafDerived Y ⟶ (pullback f).obj (structureSheafDerived X) :=
  (DerivedCategory.singleFunctor (Modules Y) 0).map
      (structureModulePullbackInv f ≫
        inv (singlePullbackHomologyComparison f
          (SheafOfModules.unit (structureSheaf X)) 0)) ≫
    lowerCohomologyInclusion ((pullback f).obj (structureSheafDerived X)) 0 inferInstance

/-- `structureSheafDerivedPullbackUnit` is `singleFunctor` of `structureModulePullbackInv`
followed by the inverse single-sheaf homology comparison and
`lowerCohomologyInclusion`. -/
theorem structureSheafDerivedPullbackUnit_eq {Y X : AlgebraicSpace S} (f : Y ⟶ X) :
    structureSheafDerivedPullbackUnit f =
      (DerivedCategory.singleFunctor (Modules Y) 0).map
          (structureModulePullbackInv f ≫
            inv (singlePullbackHomologyComparison f
              (SheafOfModules.unit (structureSheaf X)) 0)) ≫
        lowerCohomologyInclusion ((pullback f).obj (structureSheafDerived X)) 0
          inferInstance :=
  rfl

/-- The unit `𝒪_Y[0] ⟶ Lf^* 𝒪_X[0]` is inverse to `structureSheafDerivedPullbackCounit`. -/
def structureSheafDerivedPullbackUnitIso {Y X : AlgebraicSpace S} (f : Y ⟶ X) :
    structureSheafDerived Y ≅ (pullback f).obj (structureSheafDerived X) where
  hom := structureSheafDerivedPullbackUnit f
  inv := structureSheafDerivedPullbackCounit f
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The hom of `structureSheafDerivedPullbackUnitIso` is `structureSheafDerivedPullbackUnit`. -/
theorem structureSheafDerivedPullbackUnitIso_hom {Y X : AlgebraicSpace S} (f : Y ⟶ X) :
    (structureSheafDerivedPullbackUnitIso f).hom =
      structureSheafDerivedPullbackUnit f :=
  rfl

/-- The inv of `structureSheafDerivedPullbackUnitIso` is `structureSheafDerivedPullbackCounit`. -/
theorem structureSheafDerivedPullbackUnitIso_inv {Y X : AlgebraicSpace S} (f : Y ⟶ X) :
    (structureSheafDerivedPullbackUnitIso f).inv =
      structureSheafDerivedPullbackCounit f :=
  rfl

/-- Restriction of derived Hom-sections `Hom(𝒪_T[0], Lg^* K)` along a morphism of
schemes over `B`. -/
def derivedZeroRestrict (K : ModuleDerived B) {σ τ : SchemeOver B} (h : τ ⟶ σ)
    (u : structureSheafDerived (ofOver σ.left) ⟶ pullbackOver K σ) :
    structureSheafDerived (ofOver τ.left) ⟶ pullbackOver K τ :=
  structureSheafDerivedPullbackUnit ((ofOverFunctor S).map h.left) ≫
    (pullback ((ofOverFunctor S).map h.left)).map u ≫
      (pullbackCompComparison ((ofOverFunctor S).map h.left) σ.hom).app K ≫
        eqToHom (congrArg (fun k ↦ (pullback k).obj K) (CostructuredArrow.w h))

/-- The functor `T ↦ H^0(T, H^0(Lg^* K))` on schemes over `B`. -/
def cohomologyZeroFunctor (K : ModuleDerived B) :
    (SchemeOver B)ᵒᵖ ⥤ Type (u + 1) where
  obj σ :=
    SheafOfModules.unit (structureSheaf (ofOver σ.unop.left)) ⟶
      cohomologySheaf (pullbackOver K σ.unop) 0
  map h := TypeCat.ofHom (cohomologyZeroRestrict K h.unop)
  map_id := sorry
  map_comp := sorry

/-- Evaluating `cohomologyZeroFunctor K` at a scheme over `B` yields Hom from the
structure sheaf into the degree-zero cohomology sheaf of derived pullback. -/
theorem cohomologyZeroFunctor_obj (K : ModuleDerived B) (σ : SchemeOver B) :
    (cohomologyZeroFunctor K).obj (op σ) =
      (SheafOfModules.unit (structureSheaf (ofOver σ.left)) ⟶
        cohomologySheaf (pullbackOver K σ) 0) :=
  rfl

/-- `cohomologyZeroFunctor` acts on morphisms of schemes over `B` by
`cohomologyZeroRestrict`. -/
theorem cohomologyZeroFunctor_map (K : ModuleDerived B) {σ τ : SchemeOver B}
    (h : τ ⟶ σ) :
    (cohomologyZeroFunctor K).map h.op = TypeCat.ofHom (cohomologyZeroRestrict K h) :=
  rfl

/-- The functor `T ↦ H^0(T, Lg^* K)` on schemes over `B`. -/
def derivedZeroFunctor (K : ModuleDerived B) :
    (SchemeOver B)ᵒᵖ ⥤ Type (u + 1) where
  obj σ := structureSheafDerived (ofOver σ.unop.left) ⟶ pullbackOver K σ.unop
  map h := TypeCat.ofHom (derivedZeroRestrict K h.unop)
  map_id := sorry
  map_comp := sorry

/-- Evaluating `derivedZeroFunctor K` at a scheme over `B` yields derived Hom from
`𝒪_T[0]` into `Lg^* K`. -/
theorem derivedZeroFunctor_obj (K : ModuleDerived B) (σ : SchemeOver B) :
    (derivedZeroFunctor K).obj (op σ) =
      (structureSheafDerived (ofOver σ.left) ⟶ pullbackOver K σ) :=
  rfl

/-- `derivedZeroFunctor` acts on morphisms of schemes over `B` by
`derivedZeroRestrict`. -/
theorem derivedZeroFunctor_map (K : ModuleDerived B) {σ τ : SchemeOver B}
    (h : τ ⟶ σ) :
    (derivedZeroFunctor K).map h.op = TypeCat.ofHom (derivedZeroRestrict K h) :=
  rfl

/-- Under vanishing of all negative cohomology of derived pullbacks, derived Hom from
`𝒪_T[0]` agrees with global sections of `H^0(Lg^* K)`. -/
theorem derivedZeroFunctorIso_of_negativeVanishing (K : ModuleDerived B)
    (hvan : ∀ (σ : SchemeOver B) (i : ℤ), i < 0 →
      IsZero (cohomologySheaf (pullbackOver K σ) i)) :
    Nonempty (derivedZeroFunctor K ≅ cohomologyZeroFunctor K) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.ModuleDerived
