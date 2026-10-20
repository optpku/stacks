module

public import stacks_project.Chap85.Definition_85_12_1_Cartesian
public import stacks_project.Chap85.Definition_85_14_1_System

/-!
# Derived-module systems extracted from objects of D(O)

An object `K` of `D(O)` on `C_total` determines the simplicial system `(K_n, K(φ))`
with `K_n = Lg_n^* K` and `K(φ) : Lf_φ^* K_m ⟶ K_n` the canonical derived comparison.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open RingedSite

noncomputable section

universe u v w

namespace CategoryTheory.SimplicialSites

variable (C : SimplexCategory ⥤ Cat.{v, u}) (J : ∀ n, Precoverage (C.obj n))
variable [instMorphismDiagram : IsMorphismDiagram C J]
variable [instWeakSheafify : ∀ n, HasWeakSheafify (J n).toGrothendieck (Type w)]
variable [instLeftKan : ∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (C.obj m)ᵒᵖ ⥤ Type w),
    ((C.map φ).toFunctor).op.HasLeftKanExtension P]
include instMorphismDiagram instWeakSheafify instLeftKan
variable (O : Sheaf (topology C J) RingCat.{w})
variable [(topology C J).HasSheafCompose (forget RingCat.{w})]
variable [∀ n, ((J n).toGrothendieck).HasSheafCompose (forget RingCat.{w})]
variable [UnivLE.{max u v, w}]
variable [∀ n, HasSheafify ((J n).toGrothendieck) (Type w)]
variable [∀ n, ∀ P : (C.obj n)ᵒᵖ ⥤ Type w,
    (ofStage C n).op.HasPointwiseRightKanExtension P]
variable [∀ n, (SheafOfModules.restrictScalars.{w}
    (stageMorphism C J O n).structureMap).IsRightAdjoint]
variable [∀ {m n : SimplexCategory} (φ : m ⟶ n),
    (SheafOfModules.restrictScalars.{w}
      (ringedToposMap C J O φ).structureMap).IsRightAdjoint]
variable [∀ n, ToposHom.HasModulePullbackDerived (stageMorphism C J O n)]
variable [∀ {m n : SimplexCategory} (φ : m ⟶ n),
    ToposHom.HasModulePullbackDerived (ringedToposMap C J O φ)]

/-- The identity operator acts on the system extracted from `K` by the canonical
comparison `id ⟶ Lf_id^*`. -/
theorem toDerivedModuleSystem_map_id
    (K : Hom.ModuleDerived.{w} (totalRingedSite C J O)) (n : SimplexCategory) :
    (derivedPullbackIdComparisonOf (ringedToposMap C J O (𝟙 n))
          ((instHasModulePullbackFunctoriality_ringedToposMap C J O).pullbackIdIso n)).app
        ((moduleDerivedComponent C J O n).obj K) ≫
      moduleDerivedTransition C J O (𝟙 n) K =
      𝟙 ((moduleDerivedComponent C J O n).obj K) :=
  sorry

/-- Transitions of the system extracted from `K` respect composition of simplex operators
after the canonical comparison `Lf_φ^* ∘ Lf_ψ^* ⟶ Lf_{ψ ≫ φ}^*`. -/
theorem toDerivedModuleSystem_map_comp
    (K : Hom.ModuleDerived.{w} (totalRingedSite C J O))
    {l m n : SimplexCategory} (ψ : l ⟶ m) (φ : m ⟶ n) :
    (derivedPullbackCompComparisonOf (ringedToposMap C J O φ) (ringedToposMap C J O ψ)
          (ringedToposMap C J O (ψ ≫ φ))
          ((instHasModulePullbackFunctoriality_ringedToposMap C J O).pullbackCompIso ψ φ)).app
        ((moduleDerivedComponent C J O l).obj K) ≫
      moduleDerivedTransition C J O (ψ ≫ φ) K =
      (ringedToposMap C J O φ).modulePullbackDerived.map
          (moduleDerivedTransition C J O ψ K) ≫
        moduleDerivedTransition C J O φ K :=
  sorry

/-- The simplicial system `(K_n, K(φ))` of the derived category of modules attached to an
object `K` of `D(O)`, with `K_n = Lg_n^* K` and `K(φ) : Lf_φ^* K_m ⟶ K_n`. -/
def toDerivedModuleSystem (K : Hom.ModuleDerived.{w} (totalRingedSite C J O)) :
    DerivedModuleSystemOnComponents C J O :=
  DerivedModuleSystem.of (fun n ↦ (moduleDerivedComponent C J O n).obj K)
    (fun φ ↦ moduleDerivedTransition C J O φ K)
    (toDerivedModuleSystem_map_id C J O K) (toDerivedModuleSystem_map_comp C J O K)

/-- The stage object of `toDerivedModuleSystem K` at `n` is `K_n = Lg_n^* K`. -/
theorem toDerivedModuleSystem_obj
    (K : Hom.ModuleDerived.{w} (totalRingedSite C J O)) (n : SimplexCategory) :
    (toDerivedModuleSystem C J O K).obj n = (moduleDerivedComponent C J O n).obj K :=
  sorry

/-- The transition of `toDerivedModuleSystem K` at `φ` is the canonical comparison
`K(φ) : Lf_φ^* K_m ⟶ K_n`. -/
theorem toDerivedModuleSystem_map
    (K : Hom.ModuleDerived.{w} (totalRingedSite C J O))
    {m n : SimplexCategory} (φ : m ⟶ n) :
    (toDerivedModuleSystem C J O K).map φ = moduleDerivedTransition C J O φ K :=
  sorry

/-- If `K` is cartesian in `D(O)`, then the extracted system `(K_n, K(φ))` is cartesian. -/
instance instIsCartesian_toDerivedModuleSystem
    (K : Hom.ModuleDerived.{w} (totalRingedSite C J O))
    [ModuleDerived.IsCartesian C J O K] :
    DerivedModuleSystem.IsCartesian (toDerivedModuleSystem C J O K) where
  isIso_map := sorry

/-- Cartesianness of the extracted system is equivalent to cartesianness of `K` in `D(O)`. -/
theorem toDerivedModuleSystem_isCartesian_iff
    (K : Hom.ModuleDerived.{w} (totalRingedSite C J O)) :
    DerivedModuleSystem.IsCartesian (toDerivedModuleSystem C J O K) ↔
      ModuleDerived.IsCartesian C J O K :=
  sorry

/-- Naturality of stagewise derived restriction in a morphism of `D(O)`. -/
theorem toDerivedModuleSystemMap_naturality
    {K L : Hom.ModuleDerived.{w} (totalRingedSite C J O)} (α : K ⟶ L)
    {m n : SimplexCategory} (φ : m ⟶ n) :
    (toDerivedModuleSystem C J O K).map φ ≫ (moduleDerivedComponent C J O n).map α =
      (ringedToposMap C J O φ).modulePullbackDerived.map
          ((moduleDerivedComponent C J O m).map α) ≫
        (toDerivedModuleSystem C J O L).map φ :=
  sorry

/-- A morphism `α : K ⟶ L` in `D(O)` induces a morphism of the extracted derived-module
systems, acting by `Lg_n^* α` at each stage. -/
def toDerivedModuleSystemMap
    {K L : Hom.ModuleDerived.{w} (totalRingedSite C J O)} (α : K ⟶ L) :
    DerivedModuleSystem.Hom (toDerivedModuleSystem C J O K)
      (toDerivedModuleSystem C J O L) :=
  DerivedModuleSystem.homMk (fun n ↦ (moduleDerivedComponent C J O n).map α)
    (toDerivedModuleSystemMap_naturality C J O α)

/-- The stage component of `toDerivedModuleSystemMap α` at `n` is `Lg_n^* α`. -/
theorem toDerivedModuleSystemMap_app
    {K L : Hom.ModuleDerived.{w} (totalRingedSite C J O)} (α : K ⟶ L)
    (n : SimplexCategory) :
    (toDerivedModuleSystemMap C J O α).app n =
      (moduleDerivedComponent C J O n).map α :=
  sorry

end CategoryTheory.SimplicialSites
