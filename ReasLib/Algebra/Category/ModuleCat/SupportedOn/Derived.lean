module

public import ReasLib.RingTheory.Module.SectionsWithSupport
public import ReasLib.Algebra.Category.ModuleCat.Support
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat
public import ReasLib.CategoryTheory.Adjunction.Derived.Unbounded
public import ReasLib.CategoryTheory.ObjectProperty.WeakSerre

@[expose] public section

/-!
# Derived sections with support

The submodule of sections supported on a subset of a prime spectrum defines a
coreflector onto the category of supported modules. Its K-injective total
right-derived functor is the functor denoted `RH⁰_T` in the Stacks Project.
-/

open CategoryTheory

noncomputable section

universe u

namespace CategoryTheory.ModuleCat.SupportedOn

variable {A : Type u} [CommRing A]

/-- The full subcategory of `A`-modules whose support is contained in `T`. -/
abbrev category (T : Set (PrimeSpectrum A)) :=
  (ModuleCat.supportedOn T : ObjectProperty (ModuleCat.{u} A)).FullSubcategory

/-- The inclusion of modules supported on `T` into all `A`-modules. -/
abbrev inclusion (T : Set (PrimeSpectrum A)) : category T ⥤ ModuleCat.{u} A :=
  (ModuleCat.supportedOn T : ObjectProperty (ModuleCat.{u} A)).ι

/-- The module of sections of `M` supported on `T` is itself supported on `T`. -/
theorem sectionsSupported (T : Set (PrimeSpectrum A)) (M : ModuleCat.{u} A) :
    ModuleCat.supportedOn T
      (ModuleCat.of A (Module.sectionsWithSupport T M)) := sorry

/-- The supported object given by the sections of a module supported on `T`. -/
def coreflectorObj (T : Set (PrimeSpectrum A)) (M : ModuleCat.{u} A) : category T :=
  ⟨ModuleCat.of A (Module.sectionsWithSupport T M), sectionsSupported T M⟩

/-- The underlying module of the supported-sections coreflector object. -/
theorem coreflectorObj_obj (T : Set (PrimeSpectrum A)) (M : ModuleCat.{u} A) :
    (coreflectorObj T M).obj =
      ModuleCat.of A (Module.sectionsWithSupport T M) := sorry

/-- A module map sends an element supported on `T` to an element supported on `T`. -/
theorem coreflectorMapMem (T : Set (PrimeSpectrum A)) {M N : ModuleCat.{u} A}
    (f : M ⟶ N) (x : Module.sectionsWithSupport T M) :
    f.hom x ∈ Module.sectionsWithSupport T N := sorry

/-- The restriction of a module map to sections supported on `T`. -/
def coreflectorLinearMap (T : Set (PrimeSpectrum A)) {M N : ModuleCat.{u} A}
    (f : M ⟶ N) :
    Module.sectionsWithSupport T M →ₗ[A] Module.sectionsWithSupport T N :=
  (f.hom.domRestrict (Module.sectionsWithSupport T M)).codRestrict
    (Module.sectionsWithSupport T N) (coreflectorMapMem T f)

/-- The morphism between supported objects induced by a module map. -/
def coreflectorMap (T : Set (PrimeSpectrum A)) {M N : ModuleCat.{u} A}
    (f : M ⟶ N) : coreflectorObj T M ⟶ coreflectorObj T N :=
  ObjectProperty.homMk (ModuleCat.ofHom (coreflectorLinearMap T f))

/-- The ambient morphism underlying `coreflectorMap` is restriction to supported sections. -/
theorem coreflectorMap_hom (T : Set (PrimeSpectrum A)) {M N : ModuleCat.{u} A}
    (f : M ⟶ N) :
    (coreflectorMap T f).hom = ModuleCat.ofHom (coreflectorLinearMap T f) := sorry

/-- Restriction to supported sections preserves identity maps. -/
theorem coreflectorMap_id (T : Set (PrimeSpectrum A)) (M : ModuleCat.{u} A) :
    coreflectorMap T (𝟙 M) = 𝟙 (coreflectorObj T M) := sorry

/-- Restriction to supported sections preserves composition. -/
theorem coreflectorMap_comp (T : Set (PrimeSpectrum A)) {M N P : ModuleCat.{u} A}
    (f : M ⟶ N) (g : N ⟶ P) :
    coreflectorMap T (f ≫ g) = coreflectorMap T f ≫ coreflectorMap T g := sorry

/-- The supported-sections coreflector on module categories. -/
def coreflector (T : Set (PrimeSpectrum A)) : ModuleCat.{u} A ⥤ category T where
  obj := coreflectorObj T
  map := coreflectorMap T
  map_id := coreflectorMap_id T
  map_comp := coreflectorMap_comp T

/-- The supported sections of a module include canonically into that module. -/
def subtypeHom (T : Set (PrimeSpectrum A)) (M : ModuleCat.{u} A) :
    (coreflectorObj T M).obj ⟶ M :=
  ModuleCat.ofHom (Module.sectionsWithSupport T M).subtype

/-- A map from a module supported on `T` lands in the supported sections of its target. -/
theorem factorMem (T : Set (PrimeSpectrum A)) {X : category T} {M : ModuleCat.{u} A}
    (f : (inclusion T).obj X ⟶ M) (x : X.obj) :
    f.hom x ∈ Module.sectionsWithSupport T M := sorry

/-- The underlying linear map of the factorization through supported sections. -/
def factorLinearMap (T : Set (PrimeSpectrum A)) {X : category T}
    {M : ModuleCat.{u} A} (f : (inclusion T).obj X ⟶ M) :
    X.obj →ₗ[A] Module.sectionsWithSupport T M :=
  LinearMap.codRestrict (Module.sectionsWithSupport T M) f.hom (factorMem T f)

/-- The canonical factorization of a map through the target's supported sections. -/
def factor (T : Set (PrimeSpectrum A)) {X : category T} {M : ModuleCat.{u} A}
    (f : (inclusion T).obj X ⟶ M) : X ⟶ coreflectorObj T M :=
  ObjectProperty.homMk (ModuleCat.ofHom (factorLinearMap T f))

/-- Composing the canonical factor with the supported-section inclusion recovers the map. -/
theorem factor_comp_subtypeHom (T : Set (PrimeSpectrum A)) {X : category T}
    {M : ModuleCat.{u} A} (f : (inclusion T).obj X ⟶ M) :
    (factor T f).hom ≫ subtypeHom T M = f := sorry

/-- Factoring a map already landing in supported sections recovers that map. -/
theorem factor_subtypeHom_comp (T : Set (PrimeSpectrum A)) {X : category T}
    {M : ModuleCat.{u} A} (f : X ⟶ coreflectorObj T M) :
    factor T (f.hom ≫ subtypeHom T M) = f := sorry

/-- The universal Hom equivalence for the supported-sections coreflection. -/
def underivedHomEquiv (T : Set (PrimeSpectrum A))
    (X : category T) (M : ModuleCat.{u} A) :
    ((inclusion T).obj X ⟶ M) ≃ (X ⟶ (coreflector T).obj M) where
  toFun := factor T
  invFun := fun f ↦ f.hom ≫ subtypeHom T M
  left_inv := factor_comp_subtypeHom T
  right_inv := factor_subtypeHom_comp T

/-- The coreflection Hom equivalence is natural in the supported source. -/
theorem underivedHomEquiv_naturality_left_symm
    (T : Set (PrimeSpectrum A)) {X' X : category T} {M : ModuleCat.{u} A}
    (f : X' ⟶ X) (g : X ⟶ (coreflector T).obj M) :
    (underivedHomEquiv T X' M).symm (f ≫ g) =
      (inclusion T).map f ≫ (underivedHomEquiv T X M).symm g := sorry

/-- The coreflection Hom equivalence is natural in the ambient target. -/
theorem underivedHomEquiv_naturality_right
    (T : Set (PrimeSpectrum A)) {X : category T} {M N : ModuleCat.{u} A}
    (f : (inclusion T).obj X ⟶ M) (g : M ⟶ N) :
    underivedHomEquiv T X N (f ≫ g) =
      underivedHomEquiv T X M f ≫ (coreflector T).map g := sorry

/-- The inclusion of modules supported on `T` is left adjoint to supported sections. -/
def adjunction (T : Set (PrimeSpectrum A)) : inclusion T ⊣ coreflector T :=
  Adjunction.mkOfHomEquiv
    { homEquiv := underivedHomEquiv T
      homEquiv_naturality_left_symm := underivedHomEquiv_naturality_left_symm T
      homEquiv_naturality_right := underivedHomEquiv_naturality_right T }

/-- The inclusion of modules supported on `T`, bundled as an exact functor. -/
def exactInclusion (T : Set (PrimeSpectrum A)) : category T ⥤ₑ ModuleCat.{u} A :=
  ⟨inclusion T, ObjectProperty.IsWeakSerreClass.Inclusion.isExact
    (ModuleCat.supportedOn T : ObjectProperty (ModuleCat.{u} A))⟩

/-- Modules supported on `T` use the standard unbounded derived-category model. -/
@[reducible, instance]
noncomputable def hasDerivedCategory (T : Set (PrimeSpectrum A)) :
    HasDerivedCategory (category T) :=
  HasDerivedCategory.standard (category T)

/-- The supported-sections coreflector is additive. -/
instance coreflectorAdditive (T : Set (PrimeSpectrum A)) :
    (coreflector T).Additive := sorry

/-- The derived inclusion of modules supported on `T`. -/
noncomputable abbrev derivedInclusion (T : Set (PrimeSpectrum A)) :
    DerivedCategory (category T) ⥤ DerivedCategory (ModuleCat.{u} A) :=
  (exactInclusion T).obj.mapDerivedCategory

/-- The K-injective total right-derived supported-sections functor `RH⁰_T`. -/
noncomputable abbrev derivedSections (T : Set (PrimeSpectrum A)) :
    DerivedCategory (ModuleCat.{u} A) ⥤ DerivedCategory (category T) :=
  Functor.RightDerived.KInjective.functor (coreflector T)

/-- The derived inclusion is left adjoint to total right-derived supported sections. -/
noncomputable def derivedAdjunction (T : Set (PrimeSpectrum A)) :
    derivedInclusion T ⊣ derivedSections T :=
  CategoryTheory.Adjunction.Derived.KInjective.adjunction
    (exactInclusion T) (coreflector T) (adjunction T)

/-- The derived inclusion is left adjoint to total right-derived supported
sections for a Noetherian ring and a specialization-stable support. -/
noncomputable def derivedAdjunctionOfNoetherianStable {A : Type u} [CommRing A]
    [IsNoetherianRing A] (T : Set (PrimeSpectrum A))
    (hT : StableUnderSpecialization T) :
    derivedInclusion T ⊣ derivedSections T :=
  derivedAdjunction T

/-- Total right-derived supported sections is canonically a right adjoint. -/
instance derivedSectionsIsRightAdjoint (T : Set (PrimeSpectrum A)) :
    (derivedSections T).IsRightAdjoint := sorry

/-- The Hom equivalence induced by the derived supported-sections adjunction. -/
noncomputable def derivedHomEquiv (T : Set (PrimeSpectrum A))
    (K : DerivedCategory (category T)) (L : DerivedCategory (ModuleCat.{u} A)) :
    ((derivedInclusion T).obj K ⟶ L) ≃ (K ⟶ (derivedSections T).obj L) :=
  (derivedAdjunction T).homEquiv K L

end CategoryTheory.ModuleCat.SupportedOn
