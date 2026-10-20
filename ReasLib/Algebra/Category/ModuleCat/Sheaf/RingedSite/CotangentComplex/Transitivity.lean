module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.CotangentComplex.Functoriality
public import ReasLib.AlgebraicGeometry.RingedSite.Module.ChangeOfRings
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.ChangeOfRings
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Localization
public import ReasLib.CategoryTheory.Endofunctor.Iteration.Natural
public import ReasLib.CategoryTheory.Sites.AlgebraicSheaf.FreeAlgebra
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.Embedding.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplex
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
public import Mathlib.Algebra.Homology.HomotopyCategory.Shift
public import Mathlib.CategoryTheory.CommSq
public import Mathlib.CategoryTheory.Triangulated.Pretriangulated

/-!
# Transitivity triangle of sheaf cotangent complexes

For homomorphisms `A ⟶ B ⟶ C` of sheaves of rings on a site, this module owns the
canonical triangle `L(φ) ⊗^L C ⟶ L(φ ≫ ψ) ⟶ L(ψ) ⟶ (L(φ) ⊗^L C)⟦1⟧` in `D(C)`.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Pretriangulated
open HomologicalComplex
open ComplexShape
open Opposite
open AlgebraicTopology
open CochainComplex
open CochainComplex.HomComplex
open SheafOfModules.RingedSite
open scoped Simplicial
open scoped SheafOfModules.RingedSite.CotangentComplex
open scoped CategoryTheory.IteratedEndofunctor

noncomputable section

universe u

namespace SheafOfModules.RingedSite.CotangentComplex

variable {D : Type u} [Category.{u} D] {J : GrothendieckTopology D}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
variable [J.HasSheafCompose (CategoryTheory.forget CommRingCat.{u})]
variable [HasWeakSheafify J CommRingCat.{u}]
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [HasColimitsOfShape (Discrete WalkingPair) CommRingCat.{u}]
variable [UnivLE.{u, u}]

/-- Cochain-level extension of scalars of `L(φ)` along `ψ : B ⟶ C`. -/
abbrev tensorCochain {A B C : Sheaf J CommRingCat.{u}} (φ : A ⟶ B) (ψ : B ⟶ C) :
    CochainComplex (SheafOfModules (ringSheaf J C)) ℤ :=
  ((extendAlong ψ).mapHomologicalComplex (up ℤ)).obj L(φ)

/-- The image of the scalar-extended standard cotangent complex in the derived category. -/
abbrev tensor {A B C : Sheaf J CommRingCat.{u}} (φ : A ⟶ B) (ψ : B ⟶ C) :
    RingedSiteDerived J C :=
  (@DerivedCategory.Q _ inferInstance inferInstance
      (moduleCategoryHasDerivedCategory (𝒪 := C))).obj (tensorCochain φ ψ)

/-- The tensor vertex is the localization of the scalar-extended standard cotangent complex. -/
theorem tensor_eq {A B C : Sheaf J CommRingCat.{u}} (φ : A ⟶ B) (ψ : B ⟶ C) :
    tensor φ ψ = (@DerivedCategory.Q _ inferInstance inferInstance
      (moduleCategoryHasDerivedCategory (𝒪 := C))).obj (tensorCochain φ ψ) := by
  rfl

/-- Derived-functor form of `tensor`, as `SameSite.pullbackDerived` of `L(φ)`. -/
abbrev tensorDerived {A B C : Sheaf J CommRingCat.{u}} (φ : A ⟶ B) (ψ : B ⟶ C) :
    RingedSiteDerived J C :=
  (SameSite.pullbackDerived ψ).obj ((@DerivedCategory.Q _ inferInstance inferInstance
      (moduleCategoryHasDerivedCategory (𝒪 := B))).obj L(φ))

/-- Unfolding of `tensorDerived` as `SameSite.pullbackDerived` of `Q.obj L(φ)`. -/
theorem tensorDerived_eq {A B C : Sheaf J CommRingCat.{u}} (φ : A ⟶ B) (ψ : B ⟶ C) :
    tensorDerived φ ψ =
      (SameSite.pullbackDerived ψ).obj ((@DerivedCategory.Q _ inferInstance inferInstance
      (moduleCategoryHasDerivedCategory (𝒪 := B))).obj L(φ)) := by
  rfl

/-- The morphism of `Under A` corresponding to `ψ : B ⟶ C` over the composite `φ ≫ ψ`. -/
private def tensorUnderHom {A B C : Sheaf J CommRingCat.{u}} (φ : A ⟶ B) (ψ : B ⟶ C) :
    Under.mk φ ⟶ Under.mk (φ ≫ ψ) :=
  Under.homMk ψ

/-- The canonical scalar-extended cotangent map over a fixed base ring sheaf. -/
@[no_expose] def tensorMapCochain {A B C : Sheaf J CommRingCat.{u}} (φ : A ⟶ B) (ψ : B ⟶ C) :
    tensorCochain φ ψ ⟶ L(φ ≫ ψ) :=
  map (tensorUnderHom φ ψ)

/-- The first map `L(φ) ⊗^L_B C ⟶ L(φ ≫ ψ)` of the transitivity triangle in `D(C)`. -/
def tensorMap {A B C : Sheaf J CommRingCat.{u}} (φ : A ⟶ B) (ψ : B ⟶ C) :
    tensor φ ψ ⟶ (@DerivedCategory.Q _ inferInstance inferInstance
      (moduleCategoryHasDerivedCategory (𝒪 := C))).obj L(φ ≫ ψ) :=
  (@DerivedCategory.Q _ inferInstance inferInstance
      (moduleCategoryHasDerivedCategory (𝒪 := C))).map (tensorMapCochain φ ψ)

/-- The first transitivity map is the localization of the canonical map of standard complexes. -/
theorem tensorMap_eq {A B C : Sheaf J CommRingCat.{u}} (φ : A ⟶ B) (ψ : B ⟶ C) :
    tensorMap φ ψ = (@DerivedCategory.Q _ inferInstance inferInstance
      (moduleCategoryHasDerivedCategory (𝒪 := C))).map (tensorMapCochain φ ψ) := by
  rfl

/-- The second map `L(φ ≫ ψ) ⟶ L(ψ)` of the transitivity triangle in `D(C)`. -/
def toRelativeMap {A B C : Sheaf J CommRingCat.{u}} (φ : A ⟶ B) (ψ : B ⟶ C) :
    (@DerivedCategory.Q _ inferInstance inferInstance
      (moduleCategoryHasDerivedCategory (𝒪 := C))).obj L(φ ≫ ψ) ⟶ (@DerivedCategory.Q _ inferInstance inferInstance
      (moduleCategoryHasDerivedCategory (𝒪 := C))).obj L(ψ) :=
  (@DerivedCategory.Q _ inferInstance inferInstance
      (moduleCategoryHasDerivedCategory (𝒪 := C))).map (toRelativeMapCochain φ ψ)

/-- The second transitivity map is the localization of the canonical change-of-base cochain map. -/
theorem toRelativeMap_eq {A B C : Sheaf J CommRingCat.{u}} (φ : A ⟶ B) (ψ : B ⟶ C) :
    toRelativeMap φ ψ = (@DerivedCategory.Q _ inferInstance inferInstance
      (moduleCategoryHasDerivedCategory (𝒪 := C))).map (toRelativeMapCochain φ ψ) := by
  rfl

/-- The simplicial `C`-module in degree `n` underlying `tensorCochain φ ψ`. -/
abbrev tensorSimplicial {A B C : Sheaf J CommRingCat.{u}} (φ : A ⟶ B) (ψ : B ⟶ C)
    (n : SimplexCategoryᵒᵖ) : SheafOfModules (ringSheaf J C) :=
  (extendAlong ψ).obj ((simplicialModule A (Under.mk φ)).obj n)

/-- The initial algebra over a ring sheaf maps to its first free resolution term. -/
private def initialCoalgebra (B : Sheaf J CommRingCat.{u}) :
    Under.mk (𝟙 B) ⟶ (freeForgetEndo B).obj (Under.mk (𝟙 B)) :=
  Under.homMk ((freeForgetEndo B).obj (Under.mk (𝟙 B))).hom

/-- Inserting the initial-algebra coalgebra gives an extra degeneracy of its resolution. -/
private def initialExtraDegeneracy (B : Sheaf J CommRingCat.{u}) (n : ℕ) :
    standardTerm B (Under.mk (𝟙 B)) (op ⦋n⦌) ⟶
      standardTerm B (Under.mk (𝟙 B)) (op ⦋n + 1⦌) :=
  (Endofunctor.iterate (freeForgetEndo B) (n + 1)).map (initialCoalgebra B) ≫
    (IteratedEndofunctor.prependIso (freeForgetEndo B) n).hom.app (Under.mk (𝟙 B))

/-- The resolution prism factors through the extra degeneracy of the initial target algebra. -/
private def resolutionPrism {A B C : Sheaf J CommRingCat.{u}}
    (φ : A ⟶ B) (ψ : B ⟶ C) (n : ℕ) :
    (standardTerm A (Under.mk φ) (op ⦋n⦌)).right ⟶
      (standardTerm B (Under.mk ψ) (op ⦋n + 1⦌)).right :=
  standardTermRightHom (B := Under.mk φ) (B' := Under.mk (𝟙 B)) φ (𝟙 B) (op ⦋n⦌) ≫
    (initialExtraDegeneracy B n).right ≫
    (standardTermMap (Under.homMk ψ : Under.mk (𝟙 B) ⟶ Under.mk ψ) (op ⦋n + 1⦌)).right

/-- The resolution prism respects the base-ring square and the augmentations. -/
private theorem transitivityNullhomotopy_components_spec
    {A B C : Sheaf J CommRingCat.{u}} (φ : A ⟶ B) (ψ : B ⟶ C) (n : ℕ) :
    CommSq φ (standardTerm A (Under.mk φ) (op ⦋n⦌)).hom
      (standardTerm B (Under.mk ψ) (op ⦋n + 1⦌)).hom (resolutionPrism φ ψ n) ∧
    ringSheafMap (standardAugmentation A (Under.mk φ) (op ⦋n⦌) ≫ ψ) =
      ringSheafMap (resolutionPrism φ ψ n) ≫
        ringSheafMap (standardAugmentation B (Under.mk ψ) (op ⦋n + 1⦌)) := by
  sorry

/-- The prism on differentials, augmented and extended to the final ring sheaf. -/
private def prismModule {A B C : Sheaf J CommRingCat.{u}}
    (φ : A ⟶ B) (ψ : B ⟶ C) (n : ℕ) :
    tensorSimplicial φ ψ (op ⦋n⦌) ⟶
      (simplicialModule B (Under.mk ψ)).obj (op ⦋n + 1⦌) :=
  ((extendRestrictAdj ψ).homEquiv _ _).symm
    (((extendRestrictAdj (standardAugmentation A (Under.mk φ) (op ⦋n⦌))).homEquiv _ _).symm
      (RelativeDifferentials.map (transitivityNullhomotopy_components_spec φ ψ n).1 ≫
        (restrictionAlong (resolutionPrism φ ψ n)).map
          ((extendRestrictAdj (standardAugmentation B (Under.mk ψ) (op ⦋n + 1⦌))).unit.app _) ≫
        (SheafOfModules.Restriction.compIso'
          (ringSheafMap (resolutionPrism φ ψ n))
          (ringSheafMap (standardAugmentation B (Under.mk ψ) (op ⦋n + 1⦌)))
          (ringSheafMap (standardAugmentation A (Under.mk φ) (op ⦋n⦌) ≫ ψ))
          (transitivityNullhomotopy_components_spec φ ψ n).2).hom.app _ ≫
        (SheafOfModules.Restriction.compIso'
          (ringSheafMap (standardAugmentation A (Under.mk φ) (op ⦋n⦌)))
          (ringSheafMap ψ)
          (ringSheafMap (standardAugmentation A (Under.mk φ) (op ⦋n⦌) ≫ ψ))
          (by rfl)).inv.app _))

/-- The cochain of degree minus one obtained from the standard-resolution prism. -/
private def transitivityNullhomotopy {A B C : Sheaf J CommRingCat.{u}}
    (φ : A ⟶ B) (ψ : B ⟶ C) :
    Cochain (tensorCochain φ ψ) L(ψ) (-1) :=
  Cochain.mk fun i j _ =>
    match hi : embeddingDownNat.r i, hj : embeddingDownNat.r j with
    | some n, some m =>
      if h : n + 1 = m then
        (extendAlong ψ).map
          (extendXIso
            ((alternatingFaceMapComplex (SheafOfModules (ringSheaf J B))).obj
              (simplicialModule A (Under.mk φ))) embeddingDownNat
            (embeddingDownNat.f_eq_of_r_eq_some hi)).hom ≫
        prismModule φ ψ n ≫
        eqToHom (congrArg
          (fun k : ℕ => (simplicialModule B (Under.mk ψ)).obj (op ⦋k⦌)) h) ≫
        (extendXIso
          ((alternatingFaceMapComplex (SheafOfModules (ringSheaf J C))).obj
            (simplicialModule B (Under.mk ψ))) embeddingDownNat
          (embeddingDownNat.f_eq_of_r_eq_some hj)).inv
      else 0
    | _, _ => 0

/-- The differential of the standard-resolution prism is the composite cotangent map. -/
private theorem transitivityNullhomotopy_eq {A B C : Sheaf J CommRingCat.{u}}
    (φ : A ⟶ B) (ψ : B ⟶ C) :
    δ (-1) 0 (transitivityNullhomotopy φ ψ) =
      Cochain.ofHom (tensorMapCochain φ ψ ≫ toRelativeMapCochain φ ψ) := by
  sorry

/-- The cone of the first cotangent map maps canonically to the relative cotangent complex. -/
@[no_expose] def fromMappingConeCochain {A B C : Sheaf J CommRingCat.{u}}
    (φ : A ⟶ B) (ψ : B ⟶ C) :
    mappingCone (tensorMapCochain φ ψ) ⟶ L(ψ) :=
  mappingCone.desc (tensorMapCochain φ ψ) (transitivityNullhomotopy φ ψ)
    (toRelativeMapCochain φ ψ) (transitivityNullhomotopy_eq φ ψ)

/-- The canonical cone comparison for cotangent transitivity is a quasi-isomorphism. -/
instance fromMappingConeCochain_quasiIso {A B C : Sheaf J CommRingCat.{u}}
    (φ : A ⟶ B) (ψ : B ⟶ C) : QuasiIso (fromMappingConeCochain φ ψ) := by
  sorry

/-- The total left derived counit compares derived scalar extension with the standard complex. -/
def tensorComparison {A B C : Sheaf J CommRingCat.{u}} (φ : A ⟶ B) (ψ : B ⟶ C) :
    tensorDerived φ ψ ⟶ tensor φ ψ :=
  ((_root_.RingedSite.Hom.modulePullbackToDerived (sameSiteHom ψ)).totalLeftDerivedCounit
    (_root_.RingedSite.Hom.moduleLocalization (RingedSite.ofCommRingSheaf J B))
    (_root_.RingedSite.Hom.ModuleQis (RingedSite.ofCommRingSheaf J B))).app
      ((HomotopyCategory.quotient (SheafOfModules (ringSheaf J B)) (up ℤ)).obj L(φ)) ≫
    (@DerivedCategory.Q _ inferInstance inferInstance
      (moduleCategoryHasDerivedCategory (𝒪 := C))).map ((pullbackComplexExtendIso ψ).hom.app L(φ))

/-- The standard cotangent complex computes derived extension of scalars. -/
instance tensorComparison_isIso {A B C : Sheaf J CommRingCat.{u}}
    (φ : A ⟶ B) (ψ : B ⟶ C) : IsIso (tensorComparison φ ψ) := by
  sorry

/-- Derived scalar extension of the cotangent complex is represented by its standard complex. -/
def tensorDerivedIso {A B C : Sheaf J CommRingCat.{u}} (φ : A ⟶ B) (ψ : B ⟶ C) :
    tensorDerived φ ψ ≅ tensor φ ψ :=
  asIso (tensorComparison φ ψ)

/-- The transitivity boundary is the cone boundary after inverting the localized comparison. -/
def connectingMap {A B C : Sheaf J CommRingCat.{u}} (φ : A ⟶ B) (ψ : B ⟶ C) :
    (@DerivedCategory.Q _ inferInstance inferInstance
      (moduleCategoryHasDerivedCategory (𝒪 := C))).obj L(ψ) ⟶ (tensor φ ψ)⟦(1 : ℤ)⟧ :=
  inv ((@DerivedCategory.Q _ inferInstance inferInstance
      (moduleCategoryHasDerivedCategory (𝒪 := C))).map (fromMappingConeCochain φ ψ)) ≫
    (@DerivedCategory.Q _ inferInstance inferInstance
      (moduleCategoryHasDerivedCategory (𝒪 := C))).map (mappingCone.triangle (tensorMapCochain φ ψ)).mor₃ ≫
    ((@DerivedCategory.Q _ inferInstance inferInstance
      (moduleCategoryHasDerivedCategory (𝒪 := C))).commShiftIso (1 : ℤ)).hom.app (tensorCochain φ ψ)

/-- The transitivity boundary is the localized inverse cone comparison followed by the cone boundary. -/
theorem connectingMap_eq {A B C : Sheaf J CommRingCat.{u}} (φ : A ⟶ B) (ψ : B ⟶ C) :
    connectingMap φ ψ =
      inv ((@DerivedCategory.Q _ inferInstance inferInstance
      (moduleCategoryHasDerivedCategory (𝒪 := C))).map (fromMappingConeCochain φ ψ)) ≫
        (@DerivedCategory.Q _ inferInstance inferInstance
      (moduleCategoryHasDerivedCategory (𝒪 := C))).map (mappingCone.triangle (tensorMapCochain φ ψ)).mor₃ ≫
        ((@DerivedCategory.Q _ inferInstance inferInstance
      (moduleCategoryHasDerivedCategory (𝒪 := C))).commShiftIso (1 : ℤ)).hom.app (tensorCochain φ ψ) := by rfl

/-- The displayed transitivity triangle of sheaf cotangent complexes in `D(C)`. -/
def transitivityTriangle {A B C : Sheaf J CommRingCat.{u}} (φ : A ⟶ B) (ψ : B ⟶ C) :
    Triangle (RingedSiteDerived J C) :=
  Triangle.mk (tensorMap φ ψ) (toRelativeMap φ ψ) (connectingMap φ ψ)

/-- The first vertex of `transitivityTriangle` is `tensor φ ψ`. -/
theorem transitivityTriangle_obj₁ {A B C : Sheaf J CommRingCat.{u}} (φ : A ⟶ B)
    (ψ : B ⟶ C) :
    (transitivityTriangle φ ψ).obj₁ = tensor φ ψ := by
  rfl

/-- The second vertex of `transitivityTriangle` is `Q.obj L(φ ≫ ψ)`. -/
theorem transitivityTriangle_obj₂ {A B C : Sheaf J CommRingCat.{u}} (φ : A ⟶ B)
    (ψ : B ⟶ C) :
    (transitivityTriangle φ ψ).obj₂ = (@DerivedCategory.Q _ inferInstance inferInstance
      (moduleCategoryHasDerivedCategory (𝒪 := C))).obj L(φ ≫ ψ) := by
  rfl

/-- The third vertex of `transitivityTriangle` is `Q.obj L(ψ)`. -/
theorem transitivityTriangle_obj₃ {A B C : Sheaf J CommRingCat.{u}} (φ : A ⟶ B)
    (ψ : B ⟶ C) :
    (transitivityTriangle φ ψ).obj₃ = (@DerivedCategory.Q _ inferInstance inferInstance
      (moduleCategoryHasDerivedCategory (𝒪 := C))).obj L(ψ) := by
  rfl

/-- The first morphism of `transitivityTriangle` is `tensorMap`. -/
theorem transitivityTriangle_mor₁ {A B C : Sheaf J CommRingCat.{u}} (φ : A ⟶ B)
    (ψ : B ⟶ C) :
    (transitivityTriangle φ ψ).mor₁ = tensorMap φ ψ := by
  rfl

/-- The second morphism of `transitivityTriangle` is `toRelativeMap`. -/
theorem transitivityTriangle_mor₂ {A B C : Sheaf J CommRingCat.{u}} (φ : A ⟶ B)
    (ψ : B ⟶ C) :
    (transitivityTriangle φ ψ).mor₂ = toRelativeMap φ ψ := by
  rfl

/-- The third morphism of `transitivityTriangle` is `connectingMap`. -/
theorem transitivityTriangle_mor₃ {A B C : Sheaf J CommRingCat.{u}} (φ : A ⟶ B)
    (ψ : B ⟶ C) :
    (transitivityTriangle φ ψ).mor₃ = connectingMap φ ψ := by
  rfl

/-- Cotangent complexes of composable ring-sheaf maps form their canonical distinguished triangle. -/
@[stacks 08SZ]
theorem transitivityTriangle_distinguished {A B C : Sheaf J CommRingCat.{u}}
    (φ : A ⟶ B) (ψ : B ⟶ C) :
    transitivityTriangle φ ψ ∈ distTriang (RingedSiteDerived J C) := by
  sorry

end SheafOfModules.RingedSite.CotangentComplex
