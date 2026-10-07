module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.DeligneSystem.ProExtension
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.DeligneSystem.Triangle
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.DeligneSystem.Comparison
public import ReasLib.CategoryTheory.Pro.HomColimit
public import ReasLib.CategoryTheory.DerivedCategory.CohomologyIn.Bounded

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Functor CategoryTheory.Limits Opposite
open DerivedCategory.Bounded.CohomologyIn
open DerivedCategory.TStructure
open scoped DerivedCategory.CohomologyIn

noncomputable section

universe v

namespace AlgebraicGeometry.Scheme.ModuleDerived.DeligneSystem

variable {X U : Scheme.{v}} (j : U ⟶ X)
variable [IsNoetherian X] [IsNoetherian U] [IsOpenImmersion j]

/-- The chosen Deligne system extending a bounded coherent derived object on `U`. -/
noncomputable def extension
    (K : Dᵇ[SheafOfModules.isCoherent U.ringCatSheaf]) : DeligneSystem j :=
  Classical.choose (exists_deligneSystem_withValue K :
    ∃ S : DeligneSystem j, S.value = K)

/-- The chosen Deligne system has the prescribed restricted value. -/
theorem extension_value
    (K : Dᵇ[SheafOfModules.isCoherent U.ringCatSheaf]) :
    (extension j K).value = K := sorry

/-- The selected Deligne system's value, identified with the object it extends. -/
noncomputable def extensionValueIso
    (system : (K : Dᵇ[SheafOfModules.isCoherent U.ringCatSheaf]) → DeligneSystem j)
    (value_eq : ∀ K, (system K).value = K)
    (K : Dᵇ[SheafOfModules.isCoherent U.ringCatSheaf]) :
    (system K).value ≅ K :=
  eqToIso (value_eq K)

/-- The morphism between the selected restricted values induced by `f`. -/
noncomputable def extensionValueMap
    (system : (K : Dᵇ[SheafOfModules.isCoherent U.ringCatSheaf]) → DeligneSystem j)
    (value_eq : ∀ K, (system K).value = K)
    {K L : Dᵇ[SheafOfModules.isCoherent U.ringCatSheaf]} (f : K ⟶ L) :
    (ambient (SheafOfModules.isCoherent U.ringCatSheaf)).obj (system K).value ⟶
      (ambient (SheafOfModules.isCoherent U.ringCatSheaf)).obj (system L).value :=
  (ambient (SheafOfModules.isCoherent U.ringCatSheaf)).map
    ((extensionValueIso j system value_eq K).hom ≫ f ≫
      (extensionValueIso j system value_eq L).inv)

/-- The restriction-compatible lift of a morphism to the chosen Deligne pro-objects. -/
noncomputable def extensionMap
    {K L : Dᵇ[SheafOfModules.isCoherent U.ringCatSheaf]} (f : K ⟶ L) :
    (extension j K).proObject ⟶ (extension j L).proObject :=
  Classical.choose (existsUnique_proHom_restrictsTo (extension j K)
    (extension j L) (extensionValueMap j (extension j) (extension_value j) f))

/-- The chosen lift of a morphism restricts to the original morphism. -/
theorem extensionMap_restrictsTo
    {K L : Dᵇ[SheafOfModules.isCoherent U.ringCatSheaf]} (f : K ⟶ L) :
    RestrictsTo (extension j K) (extension j L) (extensionMap j f)
      (extensionValueMap j (extension j) (extension_value j) f) := sorry

/-- The chosen lift preserves identity morphisms. -/
theorem extensionMap_id (K : Dᵇ[SheafOfModules.isCoherent U.ringCatSheaf]) :
    extensionMap j (𝟙 K) = 𝟙 (extension j K).proObject := sorry

/-- The chosen lift preserves composition. -/
theorem extensionMap_comp
    {K L M : Dᵇ[SheafOfModules.isCoherent U.ringCatSheaf]}
    (f : K ⟶ L) (g : L ⟶ M) :
    extensionMap j (f ≫ g) = extensionMap j f ≫ extensionMap j g := sorry

/-- The restriction-compatible comparison from any Deligne presentation to the chosen one. -/
noncomputable def extensionIso
    (S : DeligneSystem j) (K : Dᵇ[SheafOfModules.isCoherent U.ringCatSheaf])
    (e : S.value ≅ K) :
    S.proObject ≅ (extension j K).proObject :=
  Classical.choose (existsUnique_proIso_restrictsTo K S (extension j K) e
    (eqToIso (extension_value j K)))

/-- The comparison with the chosen Deligne presentation has the prescribed restriction. -/
theorem extensionIso_restrictsTo
    (S : DeligneSystem j) (K : Dᵇ[SheafOfModules.isCoherent U.ringCatSheaf])
    (e : S.value ≅ K) :
    RestrictsTo S (extension j K) (extensionIso j S K e).hom
      ((ambient (SheafOfModules.isCoherent U.ringCatSheaf)).map
        (e.hom ≫ (eqToIso (extension_value j K)).inv)) := sorry

/-- Every stage of a Deligne tower is a bounded derived object. -/
theorem tower_obj_bounded (S : DeligneSystem j) (n : OrderDual ℕ+) :
    (t.bounded : ObjectProperty (DerivedCategory X.Modules)) (S.tower.obj n) := sorry

/-- The Deligne tower lifted to the bounded derived category. -/
noncomputable def boundedTowerInBounded (S : DeligneSystem j) :
    PNatInverseSystem (DerivedCategory.Bounded X.Modules) :=
  (t.bounded : ObjectProperty (DerivedCategory X.Modules)).lift S.tower
    (tower_obj_bounded j S)

/-- Every bounded stage of a Deligne tower has coherent cohomology. -/
theorem boundedTowerInBounded_obj_coherent (S : DeligneSystem j) (n : OrderDual ℕ+) :
    (DerivedCategory.Bounded.cohomologyIn
      (SheafOfModules.isCoherent X.ringCatSheaf) :
        ObjectProperty (DerivedCategory.Bounded X.Modules))
      ((boundedTowerInBounded j S).obj n) := sorry

/-- The positive inverse system of bounded coherent derived objects underlying a Deligne
system. -/
noncomputable def boundedTower (S : DeligneSystem j) :
    PNatInverseSystem Dᵇ[SheafOfModules.isCoherent X.ringCatSheaf] :=
  (DerivedCategory.Bounded.cohomologyIn
      (SheafOfModules.isCoherent X.ringCatSheaf) :
        ObjectProperty (DerivedCategory.Bounded X.Modules)).lift
    (boundedTowerInBounded j S) (boundedTowerInBounded_obj_coherent j S)

/-- Forgetting boundedness and coherence from `boundedTower` recovers the original Deligne
tower. -/
noncomputable def boundedTowerAmbientIso (S : DeligneSystem j) :
    boundedTower j S ⋙ ambient (SheafOfModules.isCoherent X.ringCatSheaf) ≅ S.tower :=
  (Functor.associator _ _ _).symm ≪≫
    isoWhiskerRight
      ((DerivedCategory.Bounded.cohomologyIn
        (SheafOfModules.isCoherent X.ringCatSheaf) :
          ObjectProperty (DerivedCategory.Bounded X.Modules)).liftCompιIso
          (boundedTowerInBounded j S) (boundedTowerInBounded_obj_coherent j S))
      DerivedCategory.Bounded.ι ≪≫
    (t.bounded : ObjectProperty (DerivedCategory X.Modules)).liftCompιIso
      S.tower (tower_obj_bounded j S)

/-- The pro-object in the bounded coherent derived category presented by a Deligne system. -/
noncomputable def boundedProObject (S : DeligneSystem j) :
    Pro Dᵇ[SheafOfModules.isCoherent X.ringCatSheaf] :=
  (@Pro.lim Dᵇ[SheafOfModules.isCoherent X.ringCatSheaf] _
    (OrderDual ℕ+) _ _ _ _).obj (boundedTower j S)

/-- Restriction of a bounded coherent complex along `j` is bounded in the ambient derived
category on `U`. -/
theorem restriction_obj_bounded
    (L : Dᵇ[SheafOfModules.isCoherent X.ringCatSheaf]) :
    (t.bounded : ObjectProperty (DerivedCategory U.Modules))
      ((RingedSpace.modulePullbackDerived j.toShHom).obj
        ((ambient (SheafOfModules.isCoherent X.ringCatSheaf)).obj L)) := sorry

/-- Derived restriction on bounded coherent objects, before recording coherent cohomology. -/
noncomputable def restrictionInBounded (j : U ⟶ X) [IsOpenImmersion j] :
    Dᵇ[SheafOfModules.isCoherent X.ringCatSheaf] ⥤ DerivedCategory.Bounded U.Modules :=
  (t.bounded : ObjectProperty (DerivedCategory U.Modules)).lift
    (ambient (SheafOfModules.isCoherent X.ringCatSheaf) ⋙
      RingedSpace.modulePullbackDerived j.toShHom) (restriction_obj_bounded j)

/-- Bounded derived restriction along `j` has coherent cohomology. -/
theorem restrictionInBounded_obj_coherent
    (L : Dᵇ[SheafOfModules.isCoherent X.ringCatSheaf]) :
    (DerivedCategory.Bounded.cohomologyIn
      (SheafOfModules.isCoherent U.ringCatSheaf) :
        ObjectProperty (DerivedCategory.Bounded U.Modules))
      ((restrictionInBounded j).obj L) := sorry

/-- The bounded-coherent restriction functor along the open immersion `j`. -/
noncomputable def restriction (j : U ⟶ X) [IsOpenImmersion j] :
    Dᵇ[SheafOfModules.isCoherent X.ringCatSheaf] ⥤
      Dᵇ[SheafOfModules.isCoherent U.ringCatSheaf] :=
  (DerivedCategory.Bounded.cohomologyIn
      (SheafOfModules.isCoherent U.ringCatSheaf) :
        ObjectProperty (DerivedCategory.Bounded U.Modules)).lift
    (restrictionInBounded j) (restrictionInBounded_obj_coherent j)

/-- The bounded-coherent restriction Hom functor associated to a Deligne system. -/
noncomputable def boundedRestrictionHom (S : DeligneSystem j) :
    Dᵇ[SheafOfModules.isCoherent X.ringCatSheaf] ⥤ Type (v + 1) :=
  restriction j ⋙ coyoneda.obj (op S.value)

/-- The restricted value of a Deligne system maps to the restriction of each bounded coherent
stage of its tower. -/
noncomputable def boundedStageToRestriction (S : DeligneSystem j) (i : OrderDual ℕ+) :
    coyoneda.obj (op ((boundedTower j S).obj i)) ⟶ boundedRestrictionHom j S :=
  coyonedaEquiv.symm <|
    (ambient (SheafOfModules.isCoherent U.ringCatSheaf)).preimage
      ((S.restrictionIso.app i).inv)

/-- The bounded stagewise restriction maps commute with the transitions of the Deligne tower. -/
theorem boundedStageToRestriction_naturality (S : DeligneSystem j)
    {i k : (OrderDual ℕ+)ᵒᵖ} (f : i ⟶ k) :
    (((boundedTower j S).op ⋙ coyoneda).map f) ≫
        boundedStageToRestriction j S k.unop =
      boundedStageToRestriction j S i.unop ≫
        ((Functor.const (OrderDual ℕ+)ᵒᵖ).obj (boundedRestrictionHom j S)).map f := sorry

/-- The Hom-colimit comparison from the bounded coherent Deligne tower to bounded-coherent
restriction. -/
noncomputable def boundedHomColimitToRestriction (S : DeligneSystem j) :
    Pro.homColimit (boundedTower j S) ⟶ boundedRestrictionHom j S :=
  colimit.desc ((boundedTower j S).op ⋙ coyoneda) <|
    Cocone.mk (boundedRestrictionHom j S)
      { app := fun i ↦ boundedStageToRestriction j S i.unop
        naturality := fun _ _ f ↦ boundedStageToRestriction_naturality j S f }

/-- A bounded pro-morphism respects the displayed restricted morphism when its action on
Hom-colimits commutes with the Deligne restriction comparisons. -/
def BoundedRestrictsTo (S T : DeligneSystem j)
    (f : boundedProObject j S ⟶ boundedProObject j T) (α : S.value ⟶ T.value) : Prop :=
  Pro.homColimit.map f ≫ boundedHomColimitToRestriction j S =
    boundedHomColimitToRestriction j T ≫
      whiskerLeft (restriction j) (coyoneda.map α.op)

/-- A morphism of restricted values has a unique lift between the bounded coherent Deligne
pro-objects. -/
theorem existsUnique_boundedProHom_restrictsTo (S T : DeligneSystem j)
    (α : S.value ⟶ T.value) :
    ∃! f : boundedProObject j S ⟶ boundedProObject j T,
      BoundedRestrictsTo j S T f α := sorry

/-- The selected lift of a morphism between chosen bounded coherent Deligne pro-objects. -/
noncomputable def boundedExtensionMap
    {K L : Dᵇ[SheafOfModules.isCoherent U.ringCatSheaf]} (f : K ⟶ L) :
    boundedProObject j (extension j K) ⟶ boundedProObject j (extension j L) :=
  Classical.choose (existsUnique_boundedProHom_restrictsTo j (extension j K)
    (extension j L) ((extensionValueIso j (extension j) (extension_value j) K).hom ≫
      f ≫ (extensionValueIso j (extension j) (extension_value j) L).inv))

/-- The selected bounded lift has the prescribed restriction. -/
theorem boundedExtensionMap_restrictsTo
    {K L : Dᵇ[SheafOfModules.isCoherent U.ringCatSheaf]} (f : K ⟶ L) :
    BoundedRestrictsTo j (extension j K) (extension j L) (boundedExtensionMap j f)
      ((extensionValueIso j (extension j) (extension_value j) K).hom ≫ f ≫
        (extensionValueIso j (extension j) (extension_value j) L).inv) := sorry

/-- The selected bounded lift preserves identity morphisms. -/
theorem boundedExtensionMap_id
    (K : Dᵇ[SheafOfModules.isCoherent U.ringCatSheaf]) :
    boundedExtensionMap j (𝟙 K) = 𝟙 (boundedProObject j (extension j K)) := sorry

/-- The selected bounded lift preserves composition. -/
theorem boundedExtensionMap_comp
    {K L M : Dᵇ[SheafOfModules.isCoherent U.ringCatSheaf]}
    (f : K ⟶ L) (g : L ⟶ M) :
    boundedExtensionMap j (f ≫ g) = boundedExtensionMap j f ≫ boundedExtensionMap j g := sorry

/-- The bounded coherent towers of the chosen Deligne extensions and their unique restriction-compatible lifts determine an extension-by-zero functor. -/
noncomputable def extensionByZero :
    Dᵇ[SheafOfModules.isCoherent U.ringCatSheaf] ⥤
      Pro Dᵇ[SheafOfModules.isCoherent X.ringCatSheaf] where
  obj K := boundedProObject j (extension j K)
  map f := boundedExtensionMap j f
  map_id K := boundedExtensionMap_id j K
  map_comp f g := boundedExtensionMap_comp j f g

/-- On objects, `extensionByZero` is presented by the bounded coherent tower of the selected
Deligne extension. -/
theorem extensionByZero_obj
    (K : Dᵇ[SheafOfModules.isCoherent U.ringCatSheaf]) :
    (extensionByZero j).obj K = boundedProObject j (extension j K) := sorry

/-- The ambient realization of the bounded coherent tower underlying `extensionByZero` is the
original Deligne pro-object. -/
noncomputable def extensionByZero_obj_ambientIso
    (K : Dᵇ[SheafOfModules.isCoherent U.ringCatSheaf]) :
    (@Pro.lim (DerivedCategory X.Modules) _ (OrderDual ℕ+) _ _ _ _).obj
        (boundedTower j (extension j K) ⋙
          ambient (SheafOfModules.isCoherent X.ringCatSheaf)) ≅
      (extension j K).proObject :=
  (@Pro.lim (DerivedCategory X.Modules) _ (OrderDual ℕ+) _ _ _ _).mapIso
    (boundedTowerAmbientIso j (extension j K))

/-- On morphisms, `extensionByZero` is characterized by its action after bounded-coherent
restriction. -/
theorem extensionByZero_map_restrictsTo
    {K L : Dᵇ[SheafOfModules.isCoherent U.ringCatSheaf]} (f : K ⟶ L) :
    BoundedRestrictsTo j (extension j K) (extension j L) ((extensionByZero j).map f)
      ((extensionValueIso j (extension j) (extension_value j) K).hom ≫ f ≫
        (extensionValueIso j (extension j) (extension_value j) L).inv) := sorry

/-- The pro-object formed from one vertex of a positive inverse system of bounded coherent
triangles. -/
noncomputable abbrev triangleVertexPro
    (Tₓ : PNatInverseSystem
      (Pretriangulated.Triangle Dᵇ[SheafOfModules.isCoherent X.ringCatSheaf]))
    (π : Pretriangulated.Triangle
      Dᵇ[SheafOfModules.isCoherent X.ringCatSheaf] ⥤
        Dᵇ[SheafOfModules.isCoherent X.ringCatSheaf]) :
    Pro Dᵇ[SheafOfModules.isCoherent X.ringCatSheaf] :=
  (@Pro.lim Dᵇ[SheafOfModules.isCoherent X.ringCatSheaf] _
    (OrderDual ℕ+) _ _ _ _).obj (Tₓ ⋙ π)

/-- A natural map between vertices of a bounded coherent triangle system induces a morphism of
the presented pro-objects. -/
noncomputable def triangleProMap
    (Tₓ : PNatInverseSystem
      (Pretriangulated.Triangle Dᵇ[SheafOfModules.isCoherent X.ringCatSheaf]))
    {π π' : Pretriangulated.Triangle
      Dᵇ[SheafOfModules.isCoherent X.ringCatSheaf] ⥤
        Dᵇ[SheafOfModules.isCoherent X.ringCatSheaf]} (α : π ⟶ π') :
    triangleVertexPro Tₓ π ⟶ triangleVertexPro Tₓ π' :=
  (@Pro.lim Dᵇ[SheafOfModules.isCoherent X.ringCatSheaf] _
    (OrderDual ℕ+) _ _ _ _).map (whiskerLeft Tₓ α)

/-- Compatibility of the first map in a bounded coherent triangle presentation with
`extensionByZero`. -/
def FirstTriangleMapCompatible
    (T : Pretriangulated.Triangle
      Dᵇ[SheafOfModules.isCoherent U.ringCatSheaf])
    (system : PNatInverseSystem
      (Pretriangulated.Triangle Dᵇ[SheafOfModules.isCoherent X.ringCatSheaf]))
    (firstIso : triangleVertexPro system Pretriangulated.Triangle.π₁ ≅
      (extensionByZero j).obj T.obj₁)
    (secondIso : triangleVertexPro system Pretriangulated.Triangle.π₂ ≅
      (extensionByZero j).obj T.obj₂) : Prop :=
  triangleProMap system Pretriangulated.Triangle.π₁Toπ₂ ≫ secondIso.hom =
    firstIso.hom ≫ (extensionByZero j).map T.mor₁

/-- Compatibility of the second map in a bounded coherent triangle presentation with
`extensionByZero`. -/
def SecondTriangleMapCompatible
    (T : Pretriangulated.Triangle
      Dᵇ[SheafOfModules.isCoherent U.ringCatSheaf])
    (system : PNatInverseSystem
      (Pretriangulated.Triangle Dᵇ[SheafOfModules.isCoherent X.ringCatSheaf]))
    (secondIso : triangleVertexPro system Pretriangulated.Triangle.π₂ ≅
      (extensionByZero j).obj T.obj₂)
    (thirdIso : triangleVertexPro system Pretriangulated.Triangle.π₃ ≅
      (extensionByZero j).obj T.obj₃) : Prop :=
  triangleProMap system Pretriangulated.Triangle.π₂Toπ₃ ≫ thirdIso.hom =
    secondIso.hom ≫ (extensionByZero j).map T.mor₂

/-- Compatibility of the third map in a bounded coherent triangle presentation with the
shifted first vertex under `extensionByZero`. -/
def ThirdTriangleMapCompatible
    (T : Pretriangulated.Triangle
      Dᵇ[SheafOfModules.isCoherent U.ringCatSheaf])
    (system : PNatInverseSystem
      (Pretriangulated.Triangle Dᵇ[SheafOfModules.isCoherent X.ringCatSheaf]))
    (thirdIso : triangleVertexPro system Pretriangulated.Triangle.π₃ ≅
      (extensionByZero j).obj T.obj₃)
    (shiftIso : triangleVertexPro system
        (Pretriangulated.Triangle.π₁ ⋙
          shiftFunctor Dᵇ[SheafOfModules.isCoherent X.ringCatSheaf] (1 : ℤ)) ≅
      (extensionByZero j).obj (T.obj₁⟦(1 : ℤ)⟧)) : Prop :=
  triangleProMap system Pretriangulated.Triangle.π₃Toπ₁ ≫ shiftIso.hom =
    thirdIso.hom ≫ (extensionByZero j).map T.mor₃

/-- A stagewise distinguished bounded coherent triangle system presenting the three values of
`extensionByZero` and their maps. -/
structure ExactTrianglePresentation
    (T : Pretriangulated.Triangle
      Dᵇ[SheafOfModules.isCoherent U.ringCatSheaf]) where
  /-- The positive inverse system of bounded coherent triangles on `X`. -/
  system : PNatInverseSystem
    (Pretriangulated.Triangle Dᵇ[SheafOfModules.isCoherent X.ringCatSheaf])
  /-- Every stage of the system is distinguished. -/
  stage_distinguished : ∀ n : ℕ+, system.stage n ∈
    distTriang Dᵇ[SheafOfModules.isCoherent X.ringCatSheaf]
  /-- Restriction of the system is the constant ambient image of the original triangle. -/
  restrictionIso : system ⋙ restrictionTriangle j ≅
    (Functor.const (OrderDual ℕ+)).obj
      ((ambient (SheafOfModules.isCoherent U.ringCatSheaf)).mapTriangle.obj T)
  /-- The first vertex presents the first extension-by-zero value. -/
  firstIso : triangleVertexPro system Pretriangulated.Triangle.π₁ ≅
    (extensionByZero j).obj T.obj₁
  /-- The second vertex presents the second extension-by-zero value. -/
  secondIso : triangleVertexPro system Pretriangulated.Triangle.π₂ ≅
    (extensionByZero j).obj T.obj₂
  /-- The third vertex presents the third extension-by-zero value. -/
  thirdIso : triangleVertexPro system Pretriangulated.Triangle.π₃ ≅
    (extensionByZero j).obj T.obj₃
  /-- The shifted first vertex presents the shift of the first extension-by-zero value. -/
  shiftIso : triangleVertexPro system
      (Pretriangulated.Triangle.π₁ ⋙
        shiftFunctor Dᵇ[SheafOfModules.isCoherent X.ringCatSheaf] (1 : ℤ)) ≅
    (extensionByZero j).obj (T.obj₁⟦(1 : ℤ)⟧)
  /-- The first triangle map agrees with the extension-by-zero map. -/
  map_first : FirstTriangleMapCompatible j T system firstIso secondIso
  /-- The second triangle map agrees with the extension-by-zero map. -/
  map_second : SecondTriangleMapCompatible j T system secondIso thirdIso
  /-- The third triangle map agrees with the shifted extension-by-zero map. -/
  map_third : ThirdTriangleMapCompatible j T system thirdIso shiftIso

/-- Build an exact triangle presentation from a bounded coherent triangle system, its vertex
comparisons, and the three map-compatibility conditions. -/
def ExactTrianglePresentation.ofSystem
    {T : Pretriangulated.Triangle
      Dᵇ[SheafOfModules.isCoherent U.ringCatSheaf]}
    (system : PNatInverseSystem
      (Pretriangulated.Triangle Dᵇ[SheafOfModules.isCoherent X.ringCatSheaf]))
    (stage_distinguished : ∀ n : ℕ+, system.stage n ∈
      distTriang Dᵇ[SheafOfModules.isCoherent X.ringCatSheaf])
    (restrictionIso : system ⋙ restrictionTriangle j ≅
      (Functor.const (OrderDual ℕ+)).obj
        ((ambient (SheafOfModules.isCoherent U.ringCatSheaf)).mapTriangle.obj T))
    (firstIso : triangleVertexPro system Pretriangulated.Triangle.π₁ ≅
      (extensionByZero j).obj T.obj₁)
    (secondIso : triangleVertexPro system Pretriangulated.Triangle.π₂ ≅
      (extensionByZero j).obj T.obj₂)
    (thirdIso : triangleVertexPro system Pretriangulated.Triangle.π₃ ≅
      (extensionByZero j).obj T.obj₃)
    (shiftIso : triangleVertexPro system
        (Pretriangulated.Triangle.π₁ ⋙
          shiftFunctor Dᵇ[SheafOfModules.isCoherent X.ringCatSheaf] (1 : ℤ)) ≅
      (extensionByZero j).obj (T.obj₁⟦(1 : ℤ)⟧))
    (map_first : FirstTriangleMapCompatible j T system firstIso secondIso)
    (map_second : SecondTriangleMapCompatible j T system secondIso thirdIso)
    (map_third : ThirdTriangleMapCompatible j T system thirdIso shiftIso) :
    ExactTrianglePresentation j T where
  system := system
  stage_distinguished := stage_distinguished
  restrictionIso := restrictionIso
  firstIso := firstIso
  secondIso := secondIso
  thirdIso := thirdIso
  shiftIso := shiftIso
  map_first := map_first
  map_second := map_second
  map_third := map_third

/-- The first-vertex pro-object carried by an exact triangle presentation. -/
noncomputable def ExactTrianglePresentation.firstVertexPro
    {T : Pretriangulated.Triangle
      Dᵇ[SheafOfModules.isCoherent U.ringCatSheaf]}
    (P : ExactTrianglePresentation j T) :
    Pro Dᵇ[SheafOfModules.isCoherent X.ringCatSheaf] :=
  triangleVertexPro P.system Pretriangulated.Triangle.π₁

/-- `extensionByZero` sends every distinguished triangle to a pro-triangle admitting a positive stagewise distinguished bounded coherent presentation on `X`. -/
theorem extensionByZero_exact
    (T : Pretriangulated.Triangle
      Dᵇ[SheafOfModules.isCoherent U.ringCatSheaf])
    (hT : T ∈ Pretriangulated.distinguishedTriangles) :
    Nonempty (ExactTrianglePresentation j T) := sorry

/-- The canonical Hom-colimit equivalence for a presented bounded coherent pro-object. -/
noncomputable def proHomColimitEquiv
    (A : PNatInverseSystem Dᵇ[SheafOfModules.isCoherent X.ringCatSheaf])
    (L : Dᵇ[SheafOfModules.isCoherent X.ringCatSheaf]) :
    ((@Pro.lim Dᵇ[SheafOfModules.isCoherent X.ringCatSheaf] _
      (OrderDual ℕ+) _ _ _ _).obj A ⟶ Pro.yoneda.obj L) ≃
        (Pro.homColimit A).obj L :=
  (FullyFaithful.homEquiv Pro.inclusion.fullyFaithful).trans <|
    (opEquiv _ _).trans <|
      (Iso.homCongr (Coyoneda.opIso.app (op L)) (Pro.limInclusionIso A)).trans
        coyonedaEquiv

/-- The forward bounded-coherent Hom comparison from extension by zero to restriction. -/
noncomputable def extensionByZeroHomMap
    (K : Dᵇ[SheafOfModules.isCoherent U.ringCatSheaf])
    (L : Dᵇ[SheafOfModules.isCoherent X.ringCatSheaf]) :
    ((extensionByZero j).obj K ⟶ Pro.yoneda.obj L) →
      (K ⟶ (restriction j).obj L) :=
  fun f ↦
    (extensionValueIso j (extension j) (extension_value j) K).inv ≫
      (boundedHomColimitToRestriction j (extension j K)).app L
        (proHomColimitEquiv (boundedTower j (extension j K)) L f)

/-- Extension by zero is formally left adjoint to bounded-coherent restriction: its natural Hom comparison into the constant pro-object on `L` is bijective. -/
theorem extensionByZeroHomMap_bijective
    (K : Dᵇ[SheafOfModules.isCoherent U.ringCatSheaf])
    (L : Dᵇ[SheafOfModules.isCoherent X.ringCatSheaf]) :
    Function.Bijective (extensionByZeroHomMap j K L) := sorry

/-- The extension-by-zero Hom comparison is contravariantly natural in its source. -/
theorem extensionByZeroHomMap_naturality_left
    {K K' : Dᵇ[SheafOfModules.isCoherent U.ringCatSheaf]} (f : K ⟶ K')
    (L : Dᵇ[SheafOfModules.isCoherent X.ringCatSheaf])
    (a : (extensionByZero j).obj K' ⟶ Pro.yoneda.obj L) :
    extensionByZeroHomMap j K L ((extensionByZero j).map f ≫ a) =
      f ≫ extensionByZeroHomMap j K' L a := sorry

/-- The extension-by-zero Hom comparison is covariantly natural in its constant target. -/
theorem extensionByZeroHomMap_naturality_right
    (K : Dᵇ[SheafOfModules.isCoherent U.ringCatSheaf])
    {L L' : Dᵇ[SheafOfModules.isCoherent X.ringCatSheaf]} (g : L ⟶ L')
    (a : (extensionByZero j).obj K ⟶ Pro.yoneda.obj L) :
    extensionByZeroHomMap j K L' (a ≫ (Pro.yoneda.map g)) =
      extensionByZeroHomMap j K L a ≫ (restriction j).map g := sorry

end DeligneSystem

end ModuleDerived

end Scheme

end AlgebraicGeometry
