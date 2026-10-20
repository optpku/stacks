module

public import ReasLib.Algebra.Module.IdealPower.Predicate
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.CategoryTheory.Abelian.Subcategory
public import Mathlib.CategoryTheory.Limits.ExactFunctor

/-!
# Ideal-power-torsion modules

The modules whose elements are annihilated by powers of a fixed ideal form an abelian full
subcategory. The primary-component construction is a coreflector onto this subcategory, and its
inclusion into the ambient module category is exact.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace CategoryTheory.ModuleCat

variable {A : Type u} [CommRing A]

/-- The zero module is ideal-power torsion. -/
instance isIdealPowerTorsion_containsZero (I : Ideal A) :
    ObjectProperty.ContainsZero
      ((fun M : ModuleCat.{u} A ↦ Module.IsIdealPowerTorsion I M) :
        ObjectProperty (ModuleCat.{u} A)) := sorry

/-- Ideal-power-torsion modules are closed under kernels. -/
instance isIdealPowerTorsion_isClosedUnderKernels (I : Ideal A) :
    ObjectProperty.IsClosedUnderKernels
      ((fun M : ModuleCat.{u} A ↦ Module.IsIdealPowerTorsion I M) :
        ObjectProperty (ModuleCat.{u} A)) := sorry

/-- Ideal-power-torsion modules are closed under cokernels. -/
instance isIdealPowerTorsion_isClosedUnderCokernels (I : Ideal A) :
    ObjectProperty.IsClosedUnderCokernels
      ((fun M : ModuleCat.{u} A ↦ Module.IsIdealPowerTorsion I M) :
        ObjectProperty (ModuleCat.{u} A)) := sorry

/-- Ideal-power-torsion modules are closed under finite products. -/
instance isIdealPowerTorsion_isClosedUnderFiniteProducts (I : Ideal A) :
    ObjectProperty.IsClosedUnderFiniteProducts
      ((fun M : ModuleCat.{u} A ↦ Module.IsIdealPowerTorsion I M) :
        ObjectProperty (ModuleCat.{u} A)) := sorry

namespace IdealPowerTorsion

/-- The full subcategory of `A`-modules that are power torsion for `I`. -/
abbrev category (I : Ideal A) :=
  ObjectProperty.FullSubcategory
    ((fun M : ModuleCat.{u} A ↦ Module.IsIdealPowerTorsion I M) :
      ObjectProperty (ModuleCat.{u} A))

/-- Ideal-power-torsion modules form an abelian category. -/
noncomputable instance categoryAbelian (I : Ideal A) : Abelian (category I) :=
  CategoryTheory.ObjectProperty.instAbelianFullSubcategoryOfContainsZeroOfIsClosedUnderKernelsOfIsClosedUnderCokernelsOfIsClosedUnderFiniteProducts
    ((fun M : ModuleCat.{u} A ↦ Module.IsIdealPowerTorsion I M) :
      ObjectProperty (ModuleCat.{u} A))

/-- The inclusion of ideal-power-torsion modules into all `A`-modules. -/
abbrev inclusion (I : Ideal A) : category I ⥤ ModuleCat.{u} A :=
  ObjectProperty.ι
    ((fun M : ModuleCat.{u} A ↦ Module.IsIdealPowerTorsion I M) :
      ObjectProperty (ModuleCat.{u} A))

/-- The primary component of a module is itself ideal-power torsion. -/
theorem primaryComponent_isIdealPowerTorsion (I : Ideal A) (M : ModuleCat.{u} A) :
    Module.IsIdealPowerTorsion I (I.primaryComponent M) := sorry

/-- The ideal-power-torsion object given by the primary component of a module. -/
def coreflectorObj (I : Ideal A) (M : ModuleCat.{u} A) : category I :=
  ⟨ModuleCat.of A (I.primaryComponent M), primaryComponent_isIdealPowerTorsion I M⟩

/-- Restriction of a module map to primary components. -/
def coreflectorMap (I : Ideal A) {M N : ModuleCat.{u} A} (f : M ⟶ N) :
    coreflectorObj I M ⟶ coreflectorObj I N :=
  ObjectProperty.homMk (ModuleCat.ofHom (Ideal.primaryComponent.map I f.hom))

/-- Restriction to primary components preserves identity maps. -/
theorem coreflectorMap_id (I : Ideal A) (M : ModuleCat.{u} A) :
    coreflectorMap I (𝟙 M) = 𝟙 (coreflectorObj I M) := sorry

/-- Restriction to primary components preserves composition. -/
theorem coreflectorMap_comp (I : Ideal A) {M N P : ModuleCat.{u} A}
    (f : M ⟶ N) (g : N ⟶ P) :
    coreflectorMap I (f ≫ g) = coreflectorMap I f ≫ coreflectorMap I g := sorry

/-- The primary-component coreflector on module categories. -/
def coreflector (I : Ideal A) : ModuleCat.{u} A ⥤ category I where
  obj := coreflectorObj I
  map := coreflectorMap I
  map_id := coreflectorMap_id I
  map_comp := coreflectorMap_comp I

/-- The primary component includes canonically into its ambient module. -/
def subtypeHom (I : Ideal A) (M : ModuleCat.{u} A) :
    (coreflectorObj I M).obj ⟶ M :=
  ModuleCat.ofHom (I.primaryComponent M).subtype

/-- A map from an ideal-power-torsion module lands in the target primary component. -/
theorem factor_mem (I : Ideal A) {X : category I} {M : ModuleCat.{u} A}
    (f : (inclusion I).obj X ⟶ M) (x : X.obj) :
    f.hom x ∈ I.primaryComponent M := sorry

/-- The underlying linear map of the factorization through a primary component. -/
def factorLinearMap (I : Ideal A) {X : category I} {M : ModuleCat.{u} A}
    (f : (inclusion I).obj X ⟶ M) :
    X.obj →ₗ[A] I.primaryComponent M :=
  LinearMap.codRestrict (I.primaryComponent M) f.hom (factor_mem I f)

/-- The canonical factorization of a map through the target primary component. -/
def factor (I : Ideal A) {X : category I} {M : ModuleCat.{u} A}
    (f : (inclusion I).obj X ⟶ M) : X ⟶ coreflectorObj I M :=
  ObjectProperty.homMk (ModuleCat.ofHom (factorLinearMap I f))

/-- Composing the canonical factor with the primary-component inclusion recovers the map. -/
theorem factor_comp_subtypeHom (I : Ideal A) {X : category I} {M : ModuleCat.{u} A}
    (f : (inclusion I).obj X ⟶ M) :
    (factor I f).hom ≫ subtypeHom I M = f := sorry

/-- Factoring a map already landing in the primary component recovers that map. -/
theorem factor_subtypeHom_comp (I : Ideal A) {X : category I} {M : ModuleCat.{u} A}
    (f : X ⟶ coreflectorObj I M) :
    factor I (f.hom ≫ subtypeHom I M) = f := sorry

/-- The universal Hom equivalence for the primary-component coreflection. -/
def underivedHomEquiv (I : Ideal A) (X : category I) (M : ModuleCat.{u} A) :
    ((inclusion I).obj X ⟶ M) ≃ (X ⟶ (coreflector I).obj M) where
  toFun := factor I
  invFun := fun f ↦ f.hom ≫ subtypeHom I M
  left_inv := factor_comp_subtypeHom I
  right_inv := factor_subtypeHom_comp I

/-- The coreflection Hom equivalence is natural in the torsion source. -/
theorem underivedHomEquiv_naturality_left_symm
    (I : Ideal A) {X' X : category I} {M : ModuleCat.{u} A}
    (f : X' ⟶ X) (g : X ⟶ (coreflector I).obj M) :
    (underivedHomEquiv I X' M).symm (f ≫ g) =
      (inclusion I).map f ≫ (underivedHomEquiv I X M).symm g := sorry

/-- The coreflection Hom equivalence is natural in the ambient target. -/
theorem underivedHomEquiv_naturality_right
    (I : Ideal A) {X : category I} {M N : ModuleCat.{u} A}
    (f : (inclusion I).obj X ⟶ M) (g : M ⟶ N) :
    underivedHomEquiv I X N (f ≫ g) =
      underivedHomEquiv I X M f ≫ (coreflector I).map g := sorry

/-- The inclusion of ideal-power-torsion modules is left adjoint to the primary-component
coreflector. -/
def adjunction (I : Ideal A) : inclusion I ⊣ coreflector I :=
  Adjunction.mkOfHomEquiv
    { homEquiv := underivedHomEquiv I
      homEquiv_naturality_left_symm := underivedHomEquiv_naturality_left_symm I
      homEquiv_naturality_right := underivedHomEquiv_naturality_right I }

/-- The inclusion of ideal-power-torsion modules preserves finite limits. -/
instance inclusionPreservesFiniteLimits (I : Ideal A) :
    PreservesFiniteLimits (inclusion I) := sorry

/-- The inclusion of ideal-power-torsion modules preserves finite colimits. -/
instance inclusionPreservesFiniteColimits (I : Ideal A) :
    PreservesFiniteColimits (inclusion I) := sorry

/-- The inclusion of ideal-power-torsion modules, bundled as an exact functor. -/
def exactInclusion (I : Ideal A) : category I ⥤ₑ ModuleCat.{u} A :=
  ⟨inclusion I, inclusionPreservesFiniteLimits I, inclusionPreservesFiniteColimits I⟩

/-- The primary-component coreflector is additive. -/
instance coreflectorAdditive (I : Ideal A) : (coreflector I).Additive := sorry

end IdealPowerTorsion

end CategoryTheory.ModuleCat

end
