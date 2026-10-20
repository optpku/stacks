module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.TensorUnit
public import ReasLib.AlgebraicGeometry.Scheme.Module.Pullback.Monoidal
public import ReasLib.AlgebraicGeometry.Scheme.Module.ZeroScheme.TensorSplitting.FirstProjection
public import ReasLib.AlgebraicGeometry.Scheme.Module.ZeroScheme.TensorSplitting.Over
public import ReasLib.AlgebraicGeometry.Scheme.UniversallyCatenary
public import ReasLib.Topology.Specialization.Dimension

/-!
# Unit-factor tensor-section splittings

This file records the normalization of a section as a tensor product with the
monoidal unit, its behavior under pullback, and the resulting geometric
splitting constructions.
-/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

/-- A section of `L` regarded, through the left unitor, as a section of
`(𝟙_ X.Modules) ⊗ L`. -/
noncomputable def unitTensorSection (L : X.Modules) (s : L.sections) :
    ((𝟙_ X.Modules) ⊗ L).sections :=
  SheafOfModules.sectionsMap (λ_ L).inv s

/-- The unit-tensor section is obtained by transporting a section through the
inverse left unitor. -/
theorem unitTensorSection_def (L : X.Modules) (s : L.sections) :
    unitTensorSection L s = SheafOfModules.sectionsMap (λ_ L).inv s := sorry

/-- The canonical comparison from the raw pullback of a unit tensor product to
the normalized unit tensor product. -/
noncomputable def pullbackUnitTensorIso {Y : Scheme.{u}} (f : Y ⟶ X) (L : X.Modules) :
    (pullback f).obj (𝟙_ X.Modules) ⊗ (pullback f).obj L ≅
      (𝟙_ Y.Modules) ⊗ (pullback f).obj L :=
  pullbackUnitIso f ⊗ᵢ Iso.refl ((pullback f).obj L)

/-- The pullback unit-tensor comparison is induced by `pullbackUnitIso` on the
unit factor and the identity on the second factor. -/
theorem pullbackUnitTensorIso_def {Y : Scheme.{u}} (f : Y ⟶ X) (L : X.Modules) :
    pullbackUnitTensorIso f L =
      pullbackUnitIso f ⊗ᵢ Iso.refl ((pullback f).obj L) := sorry

/-- Pulling back a unit-tensor section and applying the canonical unit
comparison gives the normalized unit-tensor section. -/
theorem pullbackUnitTensorSection {Y : Scheme.{u}} (f : Y ⟶ X)
    (L : X.Modules) (s : L.sections) :
    SheafOfModules.sectionsMap (pullbackUnitTensorIso f L).hom
        (pullbackTensorSection f (unitTensorSection L s)) =
      unitTensorSection ((pullback f).obj L) (sectionsPullback f L s) := sorry

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.TensorSectionSplitting

variable {Y : Scheme.{u}} {L : Y.Modules} [Modules.Invertible L]
variable {s : L.sections}

/-- The projection from the first factor zero scheme to the original zero
scheme, transported through a chosen compatible comparison. -/
noncomputable def unitProjection
    (C : TensorSectionSplitting (𝟙_ Y.Modules) L (Modules.unitTensorSection L s))
    (e : C.baseZero ≅ zeroScheme L s) : C.zero₁ ⟶ zeroScheme L s :=
  C.p₁ ≫ e.hom

/-- The transported first projection completes the commutative square with the
two zero-scheme immersions. -/
theorem unitProjection_comp
    (C : TensorSectionSplitting (𝟙_ Y.Modules) L (Modules.unitTensorSection L s))
    (e : C.baseZero ≅ zeroScheme L s)
    (h_e : e.hom ≫ zeroSchemeι L s = C.baseι) :
    C.ι₁ ≫ C.p = unitProjection C e ≫ zeroSchemeι L s := sorry

/-- The transported first projection is of finite type. -/
theorem unitProjection_finiteType
    (C : TensorSectionSplitting (𝟙_ Y.Modules) L (Modules.unitTensorSection L s))
    (e : C.baseZero ≅ zeroScheme L s) : Hom.FiniteType (unitProjection C e) := sorry

/-- The transported first projection is flat. -/
theorem unitProjection_flat
    (C : TensorSectionSplitting (𝟙_ Y.Modules) L (Modules.unitTensorSection L s))
    (e : C.baseZero ≅ zeroScheme L s) : Flat (unitProjection C e) := sorry

/-- The transported first projection has relative dimension one. -/
theorem unitProjection_relativeDimension
    (C : TensorSectionSplitting (𝟙_ Y.Modules) L (Modules.unitTensorSection L s))
    (e : C.baseZero ≅ zeroScheme L s) :
    Hom.RelativeDimension (unitProjection C e) 1 := sorry

/-- The first projection in a raw pullback splitting, transported to the zero
scheme of the normalized pulled-back section. -/
noncomputable def pullbackUnitProjection
    {X Y : Scheme.{u}} (f : Y ⟶ X) (L : X.Modules) [Modules.Invertible L]
    (s : L.sections)
    (C : TensorSectionSplitting ((Modules.pullback f).obj (𝟙_ X.Modules))
      ((Modules.pullback f).obj L)
      (Modules.pullbackTensorSection f (Modules.unitTensorSection L s)))
    (e : C.baseZero ≅ zeroScheme ((Modules.pullback f).obj L)
      (Modules.sectionsPullback f L s)) :
    C.zero₁ ⟶ zeroScheme ((Modules.pullback f).obj L)
      (Modules.sectionsPullback f L s) :=
  C.p₁ ≫ e.hom

/-- The transported projection for a raw pullback splitting completes the
base-changed commutative square. -/
theorem pullbackUnitProjection_comp
    {X Y : Scheme.{u}} (f : Y ⟶ X) (L : X.Modules) [Modules.Invertible L]
    (s : L.sections)
    (C : TensorSectionSplitting ((Modules.pullback f).obj (𝟙_ X.Modules))
      ((Modules.pullback f).obj L)
      (Modules.pullbackTensorSection f (Modules.unitTensorSection L s)))
    (e : C.baseZero ≅ zeroScheme ((Modules.pullback f).obj L)
      (Modules.sectionsPullback f L s))
    (h_e : e.hom ≫ zeroSchemeι ((Modules.pullback f).obj L)
      (Modules.sectionsPullback f L s) = C.baseι) :
    C.ι₁ ≫ C.p = pullbackUnitProjection f L s C e ≫
      zeroSchemeι ((Modules.pullback f).obj L)
        (Modules.sectionsPullback f L s) := sorry

/-- The transported first projection of a raw pullback splitting is of finite type. -/
theorem pullbackUnitProjection_finiteType
    {X Y : Scheme.{u}} (f : Y ⟶ X) (L : X.Modules) [Modules.Invertible L]
    (s : L.sections)
    (C : TensorSectionSplitting ((Modules.pullback f).obj (𝟙_ X.Modules))
      ((Modules.pullback f).obj L)
      (Modules.pullbackTensorSection f (Modules.unitTensorSection L s)))
    (e : C.baseZero ≅ zeroScheme ((Modules.pullback f).obj L)
      (Modules.sectionsPullback f L s)) :
    Hom.FiniteType (pullbackUnitProjection f L s C e) := sorry

/-- The transported first projection of a raw pullback splitting is flat. -/
theorem pullbackUnitProjection_flat
    {X Y : Scheme.{u}} (f : Y ⟶ X) (L : X.Modules) [Modules.Invertible L]
    (s : L.sections)
    (C : TensorSectionSplitting ((Modules.pullback f).obj (𝟙_ X.Modules))
      ((Modules.pullback f).obj L)
      (Modules.pullbackTensorSection f (Modules.unitTensorSection L s)))
    (e : C.baseZero ≅ zeroScheme ((Modules.pullback f).obj L)
      (Modules.sectionsPullback f L s)) :
    Flat (pullbackUnitProjection f L s C e) := sorry

/-- The transported first projection of a raw pullback splitting has relative
dimension one. -/
theorem pullbackUnitProjection_relativeDimension
    {X Y : Scheme.{u}} (f : Y ⟶ X) (L : X.Modules) [Modules.Invertible L]
    (s : L.sections)
    (C : TensorSectionSplitting ((Modules.pullback f).obj (𝟙_ X.Modules))
      ((Modules.pullback f).obj L)
      (Modules.pullbackTensorSection f (Modules.unitTensorSection L s)))
    (e : C.baseZero ≅ zeroScheme ((Modules.pullback f).obj L)
      (Modules.sectionsPullback f L s)) :
    Hom.RelativeDimension (pullbackUnitProjection f L s C e) 1 := sorry

/-- The first factor section transported to the structure module of the total
scheme. -/
noncomputable def firstStructureSection
    (C : TensorSectionSplitting (𝟙_ Y.Modules) L (Modules.unitTensorSection L s)) :
    (SheafOfModules.unit C.L.ringCatSheaf : C.L.Modules).sections :=
  SheafOfModules.sectionsMap
    ((Modules.pullbackUnitIso C.p).hom ≫
      (RingedSpace.unitIsoTensorUnit C.L.toRingedSpace).inv) C.s₁

/-- The first structure section is the canonical transport of `C.s₁` through
the pullback-unit and structure-module comparisons. -/
theorem firstStructureSection_def
    (C : TensorSectionSplitting (𝟙_ Y.Modules) L (Modules.unitTensorSection L s)) :
    firstStructureSection C =
      SheafOfModules.sectionsMap
        ((Modules.pullbackUnitIso C.p).hom ≫
          (RingedSpace.unitIsoTensorUnit C.L.toRingedSpace).inv) C.s₁ := sorry

/-- The first factor of a raw base-changed splitting, transported through
pullback composition and `pullbackUnitIso`, as a structure-module section. -/
noncomputable def pulledUnitStructureSection
    {X Y : Scheme.{u}} (f : Y ⟶ X) (L : X.Modules) [Modules.Invertible L]
    (s : L.sections)
    (C : TensorSectionSplitting ((Modules.pullback f).obj (𝟙_ X.Modules))
      ((Modules.pullback f).obj L)
      (Modules.pullbackTensorSection f (Modules.unitTensorSection L s))) :
    (SheafOfModules.unit C.L.ringCatSheaf : C.L.Modules).sections :=
  SheafOfModules.sectionsMap
    (((Modules.pullbackComp C.p f).app (𝟙_ X.Modules)).hom ≫
      (Modules.pullbackUnitIso (C.p ≫ f)).hom ≫
        (RingedSpace.unitIsoTensorUnit C.L.toRingedSpace).inv) C.s₁

/-- The pulled-unit structure section uses the canonical comparison from the
iterated pullback of the unit module to the structure module. -/
theorem pulledUnitStructureSection_def
    {X Y : Scheme.{u}} (f : Y ⟶ X) (L : X.Modules) [Modules.Invertible L]
    (s : L.sections)
    (C : TensorSectionSplitting ((Modules.pullback f).obj (𝟙_ X.Modules))
      ((Modules.pullback f).obj L)
      (Modules.pullbackTensorSection f (Modules.unitTensorSection L s))) :
    pulledUnitStructureSection f L s C =
      SheafOfModules.sectionsMap
        (((Modules.pullbackComp C.p f).app (𝟙_ X.Modules)).hom ≫
          (Modules.pullbackUnitIso (C.p ≫ f)).hom ≫
            (RingedSpace.unitIsoTensorUnit C.L.toRingedSpace).inv) C.s₁ := sorry

/-- The first zero scheme of a raw pullback splitting, regarded over the
original fixed base. -/
noncomputable def pullbackZero₁Over
    {S : Scheme.{u}} (X : Over S) {Y : Scheme.{u}} (f : Y ⟶ X.left)
    (L : X.left.Modules) [Modules.Invertible L] (s : L.sections)
    [h_unit : Modules.Invertible ((Modules.pullback f).obj (𝟙_ X.left.Modules))]
    [h_L : Modules.Invertible ((Modules.pullback f).obj L)]
    (C : TensorSectionSplitting ((Modules.pullback f).obj (𝟙_ X.left.Modules))
      ((Modules.pullback f).obj L)
      (Modules.pullbackTensorSection f (Modules.unitTensorSection L s))) : Over S :=
  @zero₁Over S (Over.mk (f ≫ X.hom))
    ((Modules.pullback f).obj (𝟙_ X.left.Modules)) ((Modules.pullback f).obj L)
    h_unit h_L
    (Modules.pullbackTensorSection f (Modules.unitTensorSection L s)) C

/-- The structure morphism of `pullbackZero₁Over` is the first zero immersion
followed by the raw splitting projection and the base-change map. -/
theorem pullbackZero₁Over_hom
    {S : Scheme.{u}} (X : Over S) {Y : Scheme.{u}} (f : Y ⟶ X.left)
    (L : X.left.Modules) [Modules.Invertible L] (s : L.sections)
    [Modules.Invertible ((Modules.pullback f).obj (𝟙_ X.left.Modules))]
    [Modules.Invertible ((Modules.pullback f).obj L)]
    (C : TensorSectionSplitting ((Modules.pullback f).obj (𝟙_ X.left.Modules))
      ((Modules.pullback f).obj L)
      (Modules.pullbackTensorSection f (Modules.unitTensorSection L s))) :
    (pullbackZero₁Over X f L s C).hom = C.ι₁ ≫ C.p ≫ (f ≫ X.hom) := sorry

/-- The first zero scheme of a locally finite-type raw pullback splitting is
locally of finite type over the original fixed base. -/
theorem pullbackZero₁Over_locallyOfFiniteType
    {S : Scheme.{u}} (X : Over S) [LocallyOfFiniteType X.hom]
    {Y : Scheme.{u}} (f : Y ⟶ X.left) [LocallyOfFiniteType f]
    (L : X.left.Modules) [Modules.Invertible L] (s : L.sections)
    [Modules.Invertible ((Modules.pullback f).obj (𝟙_ X.left.Modules))]
    [Modules.Invertible ((Modules.pullback f).obj L)]
    (C : TensorSectionSplitting ((Modules.pullback f).obj (𝟙_ X.left.Modules))
      ((Modules.pullback f).obj L)
      (Modules.pullbackTensorSection f (Modules.unitTensorSection L s))) :
    LocallyOfFiniteType (pullbackZero₁Over X f L s C).hom := sorry

/-- For a raw unit-factor pullback splitting, the first zero scheme is the
zero scheme of the canonically transported structure-module section. -/
theorem existsPulledUnitStructureZeroScheme
    {X Y : Scheme.{u}} (f : Y ⟶ X) (L : X.Modules) [Modules.Invertible L]
    (s : L.sections)
    [Modules.Invertible ((Modules.pullback f).obj (𝟙_ X.Modules))]
    [Modules.Invertible ((Modules.pullback f).obj L)]
    (C : TensorSectionSplitting ((Modules.pullback f).obj (𝟙_ X.Modules))
      ((Modules.pullback f).obj L)
      (Modules.pullbackTensorSection f (Modules.unitTensorSection L s))) :
    ∃ e' : C.zero₁ ≅
        zeroScheme (SheafOfModules.unit C.L.ringCatSheaf : C.L.Modules)
          (pulledUnitStructureSection f L s C),
      e'.hom ≫ zeroSchemeι
        (SheafOfModules.unit C.L.ringCatSheaf : C.L.Modules)
        (pulledUnitStructureSection f L s C) = C.ι₁ := sorry

/-- The chosen zero-scheme comparison regarded as an isomorphism over the
fixed base scheme. -/
noncomputable def unitBaseZeroOverIso {S : Scheme.{u}} (X : Over S)
    (L : X.left.Modules) [Modules.Invertible L] (s : L.sections)
    (C : TensorSectionSplitting (𝟙_ X.left.Modules) L (Modules.unitTensorSection L s))
    (e : C.baseZero ≅ zeroScheme L s)
    (h_e : e.hom ≫ zeroSchemeι L s = C.baseι) :
    baseZeroOver X C ≅ Over.mk (zeroSchemeι L s ≫ X.hom) :=
  by
    change (Over.map X.hom).obj (Over.mk C.baseι) ≅
      (Over.map X.hom).obj (Over.mk (zeroSchemeι L s))
    exact (Over.map X.hom).mapIso (Over.isoMk e h_e)

/-- The underlying scheme map of `unitBaseZeroOverIso` is the chosen
zero-scheme isomorphism. -/
theorem unitBaseZeroOverIso_hom_left {S : Scheme.{u}} (X : Over S)
    (L : X.left.Modules) [Modules.Invertible L] (s : L.sections)
    (C : TensorSectionSplitting (𝟙_ X.left.Modules) L (Modules.unitTensorSection L s))
    (e : C.baseZero ≅ zeroScheme L s)
    (h_e : e.hom ≫ zeroSchemeι L s = C.baseι) :
    (unitBaseZeroOverIso X L s C e h_e).hom.left = e.hom := sorry

/-- The chosen comparison for a raw pullback splitting regarded as an
isomorphism over the original fixed base. -/
noncomputable def pullbackUnitBaseZeroOverIso
    {S : Scheme.{u}} (X : Over S) {Y : Scheme.{u}} (f : Y ⟶ X.left)
    (L : X.left.Modules) [Modules.Invertible L] (s : L.sections)
    [h_unit : Modules.Invertible ((Modules.pullback f).obj (𝟙_ X.left.Modules))]
    [h_L : Modules.Invertible ((Modules.pullback f).obj L)]
    (C : TensorSectionSplitting ((Modules.pullback f).obj (𝟙_ X.left.Modules))
      ((Modules.pullback f).obj L)
      (Modules.pullbackTensorSection f (Modules.unitTensorSection L s)))
    (e : C.baseZero ≅ zeroScheme ((Modules.pullback f).obj L)
      (Modules.sectionsPullback f L s))
    (h_e : e.hom ≫ zeroSchemeι ((Modules.pullback f).obj L)
      (Modules.sectionsPullback f L s) = C.baseι) :
    @baseZeroOver S (Over.mk (f ≫ X.hom))
        ((Modules.pullback f).obj (𝟙_ X.left.Modules))
        ((Modules.pullback f).obj L) h_unit h_L
        (Modules.pullbackTensorSection f (Modules.unitTensorSection L s)) C ≅
      Over.mk (zeroSchemeι ((Modules.pullback f).obj L)
        (Modules.sectionsPullback f L s) ≫ (f ≫ X.hom)) :=
  by
    change (Over.map (f ≫ X.hom)).obj (Over.mk C.baseι) ≅
      (Over.map (f ≫ X.hom)).obj
        (Over.mk (zeroSchemeι ((Modules.pullback f).obj L)
          (Modules.sectionsPullback f L s)))
    exact (Over.map (f ≫ X.hom)).mapIso (Over.isoMk e h_e)

/-- The underlying scheme map of `pullbackUnitBaseZeroOverIso` is the chosen
base-changed zero-scheme isomorphism. -/
theorem pullbackUnitBaseZeroOverIso_hom_left
    {S : Scheme.{u}} (X : Over S) {Y : Scheme.{u}} (f : Y ⟶ X.left)
    (L : X.left.Modules) [Modules.Invertible L] (s : L.sections)
    [Modules.Invertible ((Modules.pullback f).obj (𝟙_ X.left.Modules))]
    [Modules.Invertible ((Modules.pullback f).obj L)]
    (C : TensorSectionSplitting ((Modules.pullback f).obj (𝟙_ X.left.Modules))
      ((Modules.pullback f).obj L)
      (Modules.pullbackTensorSection f (Modules.unitTensorSection L s)))
    (e : C.baseZero ≅ zeroScheme ((Modules.pullback f).obj L)
      (Modules.sectionsPullback f L s))
    (h_e : e.hom ≫ zeroSchemeι ((Modules.pullback f).obj L)
      (Modules.sectionsPullback f L s) = C.baseι) :
    (pullbackUnitBaseZeroOverIso X f L s C e h_e).hom.left = e.hom := sorry

variable {S : Scheme.{u}} (X : Over S)
variable (L : X.left.Modules) [Modules.Invertible L]
variable (s : L.sections)
variable (C : TensorSectionSplitting (𝟙_ X.left.Modules) L
  (Modules.unitTensorSection L s))

/-- The transported first projection commutes with the structure morphisms to
the fixed base. -/
theorem unitProjection_over
    (e : C.baseZero ≅ zeroScheme L s)
    (h_e : e.hom ≫ zeroSchemeι L s = C.baseι) :
    C.unitProjection e ≫ (Over.mk (zeroSchemeι L s ≫ X.hom)).hom =
      (zero₁Over X C).hom := sorry

/-- The first projection, transported to the original zero scheme, as a
morphism over the fixed base. -/
noncomputable def unitProjectionOver
    (e : C.baseZero ≅ zeroScheme L s)
    (h_e : e.hom ≫ zeroSchemeι L s = C.baseι) :
    zero₁Over X C ⟶ Over.mk (zeroSchemeι L s ≫ X.hom) :=
  by
    change (Over.map X.hom).obj
        (Over.mk (zeroSchemeι ((Modules.pullback C.p).obj (𝟙_ X.left.Modules))
          C.s₁ ≫ C.p)) ⟶
      (Over.map X.hom).obj (Over.mk (zeroSchemeι L s))
    exact (Over.map X.hom).map (Over.homMk (C.p₁ ≫ e.hom) (by
      change (C.p₁ ≫ e.hom) ≫ zeroSchemeι L s =
        zeroSchemeι ((Modules.pullback C.p).obj (𝟙_ X.left.Modules)) C.s₁ ≫ C.p
      simp only [Category.assoc]
      rw [h_e, ← C.left_comm]))

/-- The underlying map of `unitProjectionOver` is `C.unitProjection e`. -/
theorem unitProjectionOver_left
    (e : C.baseZero ≅ zeroScheme L s)
    (h_e : e.hom ≫ zeroSchemeι L s = C.baseι) :
    (unitProjectionOver X L s C e h_e).left = C.unitProjection e := sorry

/-- The transported first projection over the fixed base is of finite type. -/
theorem unitProjectionOver_finiteType
    (e : C.baseZero ≅ zeroScheme L s)
    (h_e : e.hom ≫ zeroSchemeι L s = C.baseι) :
    Hom.FiniteType (unitProjectionOver X L s C e h_e).left := sorry

/-- The transported first projection over the fixed base is flat. -/
theorem unitProjectionOver_flat
    (e : C.baseZero ≅ zeroScheme L s)
    (h_e : e.hom ≫ zeroSchemeι L s = C.baseι) :
    Flat (unitProjectionOver X L s C e h_e).left := sorry

/-- The transported first projection over the fixed base has relative dimension one. -/
theorem unitProjectionOver_relativeDimension
    (e : C.baseZero ≅ zeroScheme L s)
    (h_e : e.hom ≫ zeroSchemeι L s = C.baseι) :
    Hom.RelativeDimension (unitProjectionOver X L s C e h_e).left 1 := sorry

/-- The source-view projection for a raw pullback splitting commutes with the
structure morphisms to the fixed base. -/
theorem pullbackUnitProjection_over
    {Y : Scheme.{u}} (f : Y ⟶ X.left) [LocallyOfFiniteType f]
    [Modules.Invertible ((Modules.pullback f).obj (𝟙_ X.left.Modules))]
    [Modules.Invertible ((Modules.pullback f).obj L)]
    (C : TensorSectionSplitting
      ((Modules.pullback f).obj (𝟙_ X.left.Modules))
      ((Modules.pullback f).obj L)
      (Modules.pullbackTensorSection f (Modules.unitTensorSection L s)))
    (e : C.baseZero ≅ zeroScheme ((Modules.pullback f).obj L)
      (Modules.sectionsPullback f L s))
    (h_e : e.hom ≫ zeroSchemeι ((Modules.pullback f).obj L)
      (Modules.sectionsPullback f L s) = C.baseι) :
    C.pullbackUnitProjection f L s e ≫
        (Over.mk (zeroSchemeι ((Modules.pullback f).obj L)
          (Modules.sectionsPullback f L s) ≫ (f ≫ X.hom))).hom =
      (pullbackZero₁Over X f L s C).hom := sorry

/-- The source-view first projection of a raw pullback splitting as a morphism
over the fixed base. -/
noncomputable def pullbackUnitProjectionOver
    {Y : Scheme.{u}} (f : Y ⟶ X.left) [LocallyOfFiniteType f]
    [Modules.Invertible ((Modules.pullback f).obj (𝟙_ X.left.Modules))]
    [Modules.Invertible ((Modules.pullback f).obj L)]
    (C : TensorSectionSplitting
      ((Modules.pullback f).obj (𝟙_ X.left.Modules))
      ((Modules.pullback f).obj L)
      (Modules.pullbackTensorSection f (Modules.unitTensorSection L s)))
    (e : C.baseZero ≅ zeroScheme ((Modules.pullback f).obj L)
      (Modules.sectionsPullback f L s))
    (h_e : e.hom ≫ zeroSchemeι ((Modules.pullback f).obj L)
      (Modules.sectionsPullback f L s) = C.baseι) :
    pullbackZero₁Over X f L s C ⟶
      Over.mk (zeroSchemeι ((Modules.pullback f).obj L)
        (Modules.sectionsPullback f L s) ≫ (f ≫ X.hom)) :=
  by
    change (Over.map (f ≫ X.hom)).obj
        (Over.mk (zeroSchemeι
          ((Modules.pullback C.p).obj ((Modules.pullback f).obj (𝟙_ X.left.Modules)))
          C.s₁ ≫ C.p)) ⟶
      (Over.map (f ≫ X.hom)).obj
        (Over.mk (zeroSchemeι ((Modules.pullback f).obj L)
          (Modules.sectionsPullback f L s)))
    exact (Over.map (f ≫ X.hom)).map (Over.homMk (C.p₁ ≫ e.hom) (by
      change (C.p₁ ≫ e.hom) ≫ zeroSchemeι ((Modules.pullback f).obj L)
          (Modules.sectionsPullback f L s) =
        zeroSchemeι
          ((Modules.pullback C.p).obj ((Modules.pullback f).obj (𝟙_ X.left.Modules)))
          C.s₁ ≫ C.p
      simp only [Category.assoc]
      rw [h_e, ← C.left_comm]))

/-- The underlying map of `pullbackUnitProjectionOver` is the transported
first projection of the raw splitting. -/
theorem pullbackUnitProjectionOver_left
    {Y : Scheme.{u}} (f : Y ⟶ X.left) [LocallyOfFiniteType f]
    [Modules.Invertible ((Modules.pullback f).obj (𝟙_ X.left.Modules))]
    [Modules.Invertible ((Modules.pullback f).obj L)]
    (C : TensorSectionSplitting
      ((Modules.pullback f).obj (𝟙_ X.left.Modules))
      ((Modules.pullback f).obj L)
      (Modules.pullbackTensorSection f (Modules.unitTensorSection L s)))
    (e : C.baseZero ≅ zeroScheme ((Modules.pullback f).obj L)
      (Modules.sectionsPullback f L s))
    (h_e : e.hom ≫ zeroSchemeι ((Modules.pullback f).obj L)
      (Modules.sectionsPullback f L s) = C.baseι) :
    (pullbackUnitProjectionOver X L s f C e h_e).left =
      C.pullbackUnitProjection f L s e := sorry

/-- The source-view projection over the fixed base is of finite type. -/
theorem pullbackUnitProjectionOver_finiteType
    {Y : Scheme.{u}} (f : Y ⟶ X.left) [LocallyOfFiniteType f]
    [Modules.Invertible ((Modules.pullback f).obj (𝟙_ X.left.Modules))]
    [Modules.Invertible ((Modules.pullback f).obj L)]
    (C : TensorSectionSplitting
      ((Modules.pullback f).obj (𝟙_ X.left.Modules))
      ((Modules.pullback f).obj L)
      (Modules.pullbackTensorSection f (Modules.unitTensorSection L s)))
    (e : C.baseZero ≅ zeroScheme ((Modules.pullback f).obj L)
      (Modules.sectionsPullback f L s))
    (h_e : e.hom ≫ zeroSchemeι ((Modules.pullback f).obj L)
      (Modules.sectionsPullback f L s) = C.baseι) :
    Hom.FiniteType (pullbackUnitProjectionOver X L s f C e h_e).left := sorry

/-- The source-view projection over the fixed base is flat. -/
theorem pullbackUnitProjectionOver_flat
    {Y : Scheme.{u}} (f : Y ⟶ X.left) [LocallyOfFiniteType f]
    [Modules.Invertible ((Modules.pullback f).obj (𝟙_ X.left.Modules))]
    [Modules.Invertible ((Modules.pullback f).obj L)]
    (C : TensorSectionSplitting
      ((Modules.pullback f).obj (𝟙_ X.left.Modules))
      ((Modules.pullback f).obj L)
      (Modules.pullbackTensorSection f (Modules.unitTensorSection L s)))
    (e : C.baseZero ≅ zeroScheme ((Modules.pullback f).obj L)
      (Modules.sectionsPullback f L s))
    (h_e : e.hom ≫ zeroSchemeι ((Modules.pullback f).obj L)
      (Modules.sectionsPullback f L s) = C.baseι) :
    Flat (pullbackUnitProjectionOver X L s f C e h_e).left := sorry

/-- The source-view projection over the fixed base has relative dimension one. -/
theorem pullbackUnitProjectionOver_relativeDimension
    {Y : Scheme.{u}} (f : Y ⟶ X.left) [LocallyOfFiniteType f]
    [Modules.Invertible ((Modules.pullback f).obj (𝟙_ X.left.Modules))]
    [Modules.Invertible ((Modules.pullback f).obj L)]
    (C : TensorSectionSplitting
      ((Modules.pullback f).obj (𝟙_ X.left.Modules))
      ((Modules.pullback f).obj L)
      (Modules.pullbackTensorSection f (Modules.unitTensorSection L s)))
    (e : C.baseZero ≅ zeroScheme ((Modules.pullback f).obj L)
      (Modules.sectionsPullback f L s))
    (h_e : e.hom ≫ zeroSchemeι ((Modules.pullback f).obj L)
      (Modules.sectionsPullback f L s) = C.baseι) :
    Hom.RelativeDimension (pullbackUnitProjectionOver X L s f C e h_e).left 1 := sorry

end AlgebraicGeometry.Scheme.TensorSectionSplitting

namespace AlgebraicGeometry.Scheme

/-- The zero scheme of a section of an invertible module admits a unit-factor
tensor-section splitting compatible with every locally finite-type base change. -/
theorem existsUnitSplitting
    {S : Scheme.{u}} [UniversallyCatenary S]
    (delta : S → ℤ) [IsDimensionFunction delta]
    (X : Over S) [LocallyOfFiniteType X.hom]
    (L : X.left.Modules) [Modules.Invertible L] (s : L.sections) :
    ∃ C : TensorSectionSplitting (𝟙_ X.left.Modules) L
        (Modules.unitTensorSection L s),
      ∃ e : C.baseZero ≅ zeroScheme L s,
        e.hom ≫ zeroSchemeι L s = C.baseι ∧
          ∀ {Y : Scheme.{u}} (f : Y ⟶ X.left) [LocallyOfFiniteType f],
            ∃ C' : TensorSectionSplitting
              ((Modules.pullback f).obj (𝟙_ X.left.Modules))
                ((Modules.pullback f).obj L)
                (Modules.pullbackTensorSection f (Modules.unitTensorSection L s)),
              ∃ B : C.BaseChange f C',
                ∃ e' : C'.baseZero ≅
                    zeroScheme ((Modules.pullback f).obj L)
                      (Modules.sectionsPullback f L s),
                  e'.hom ≫ zeroSchemeι ((Modules.pullback f).obj L)
                      (Modules.sectionsPullback f L s) = C'.baseι := sorry

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Scheme.TensorSectionSplitting

/-- The first factor zero scheme is compatibly the zero scheme of a global
section of the structure module of the total scheme. -/
theorem existsFirstStructureZeroScheme
    {Y : Scheme.{u}} (L : Y.Modules) [Modules.Invertible L] (s : L.sections)
    (C : TensorSectionSplitting (𝟙_ Y.Modules) L (Modules.unitTensorSection L s)) :
    ∃ e' : C.zero₁ ≅
        zeroScheme (SheafOfModules.unit C.L.ringCatSheaf : C.L.Modules)
          (firstStructureSection C),
      e'.hom ≫ zeroSchemeι (SheafOfModules.unit C.L.ringCatSheaf : C.L.Modules)
          (firstStructureSection C) = C.ι₁ := sorry

end AlgebraicGeometry.Scheme.TensorSectionSplitting
