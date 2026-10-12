/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.ScalarExtension
public import ReasLib.AlgebraicGeometry.Scheme.BaseChange.Affine
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Module.Tilde.ChangeOfRings.Pullback
public import ReasLib.CategoryTheory.Adjunction.BaseChange
public import ReasLib.CategoryTheory.Adjunction.HomotopyCategory
public import ReasLib.CategoryTheory.DerivedCategory.Functor.TotalLeftDerived.Composition
public import ReasLib.CategoryTheory.DerivedCategory.Functor.TotalRightDerived.Homotopy
public import ReasLib.CategoryTheory.Functor.Derived.Adjunction.Restriction

/-!
# Derived base change for module cohomology

This file defines derived global sections over an affine base, the corresponding object after
affine base change, and the canonical comparison morphism between them.
-/

@[expose] public section

open CategoryTheory ComplexShape

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- Affine tilde sheafification followed by pullback to a scheme over the affine base. -/
abbrev affineBaseModuleAssociatedFunctor
    (A : Type u) [CommRing A] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of A)) : ModuleCat A ⥤ X.Modules :=
  tilde.functor (CommRingCat.of A) ⋙ Scheme.Modules.pullback f

/-- Pushforward to an affine base followed by global sections. -/
abbrev affineBaseModuleGlobalSectionsFunctor
    (A : Type u) [CommRing A] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of A)) : X.Modules ⥤ ModuleCat A :=
  Scheme.Modules.pushforward f ⋙
    (moduleSpecΓFunctor (R := CommRingCat.of A) :
      (Spec (CommRingCat.of A)).Modules ⥤ ModuleCat A)

/-- Affine tilde sheafification is additive. -/
private theorem affineTildeFunctorAdditive
    (A : Type u) [CommRing A] : (tilde.functor (CommRingCat.of A)).Additive :=
  let hTildeLeft : (tilde.functor (CommRingCat.of A)).IsLeftAdjoint :=
    (tilde.adjunction (R := CommRingCat.of A)).isLeftAdjoint
  let hTildeZero : (tilde.functor (CommRingCat.of A)).PreservesZeroMorphisms :=
    @Functor.preservesZeroMorphisms_of_isLeftAdjoint _ _ _ _ _ _
      (tilde.functor (CommRingCat.of A)) hTildeLeft
  let hTildeCoproducts :
      Limits.PreservesColimitsOfShape (Discrete Limits.WalkingPair)
        (tilde.functor (CommRingCat.of A)) :=
    (tilde.adjunction (R := CommRingCat.of A)).leftAdjoint_preservesColimits.preservesColimitsOfShape
  let hTildeBiproducts :
      Limits.PreservesBinaryBiproducts (tilde.functor (CommRingCat.of A)) :=
    @Limits.preservesBinaryBiproducts_of_preservesBinaryCoproducts
      _ _ _ _ _ _ (tilde.functor (CommRingCat.of A)) hTildeZero hTildeCoproducts
  @Functor.additive_of_preservesBinaryBiproducts
    _ _ _ _ _ _ (tilde.functor (CommRingCat.of A)) inferInstance
      hTildeZero hTildeBiproducts

/-- Affine associated-module formation is additive. -/
noncomputable instance affineBaseModuleAssociatedFunctorAdditive
    (A : Type u) [CommRing A] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of A)) :
    (affineBaseModuleAssociatedFunctor A f).Additive :=
  let hTilde := affineTildeFunctorAdditive A
  let hPullback : (Scheme.Modules.pullback f).Additive := inferInstance
  { map_add := by
      intro M N g h
      change
        (Scheme.Modules.pullback f).map
            ((tilde.functor (CommRingCat.of A)).map (g + h)) =
          (Scheme.Modules.pullback f).map
              ((tilde.functor (CommRingCat.of A)).map g) +
            (Scheme.Modules.pullback f).map
              ((tilde.functor (CommRingCat.of A)).map h)
      rw [hTilde.map_add (f := g) (g := h),
        hPullback.map_add
          (f := (tilde.functor (CommRingCat.of A)).map g)
          (g := (tilde.functor (CommRingCat.of A)).map h)] }

/-- Affine-base global sections are additive. -/
noncomputable instance affineBaseModuleGlobalSectionsFunctorAdditive
    (A : Type u) [CommRing A] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of A)) :
    (affineBaseModuleGlobalSectionsFunctor A f).Additive :=
  let hPushforward : (Scheme.Modules.pushforward f).Additive := inferInstance
  let hSections : (moduleSpecΓFunctor (R := CommRingCat.of A)).Additive :=
    @Adjunction.right_adjoint_additive _ _ _ _ _ _ _ _
      (tilde.adjunction (R := CommRingCat.of A)) (affineTildeFunctorAdditive A)
  { map_add := by
      intro M N g h
      change
        (moduleSpecΓFunctor (R := CommRingCat.of A)).map
            ((Scheme.Modules.pushforward f).map (g + h)) =
          (moduleSpecΓFunctor (R := CommRingCat.of A)).map
              ((Scheme.Modules.pushforward f).map g) +
            (moduleSpecΓFunctor (R := CommRingCat.of A)).map
              ((Scheme.Modules.pushforward f).map h)
      rw [hPushforward.map_add (f := g) (g := h),
        hSections.map_add
          (f := (Scheme.Modules.pushforward f).map g)
          (g := (Scheme.Modules.pushforward f).map h)] }

/-- Affine associated modules and affine-base global sections form the composite tilde-pullback
adjunction. -/
noncomputable def affineBaseModuleAdjunction
    (A : Type u) [CommRing A] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of A)) :
    affineBaseModuleAssociatedFunctor A f ⊣ affineBaseModuleGlobalSectionsFunctor A f :=
  (tilde.adjunction (R := CommRingCat.of A)).comp
    (Scheme.Modules.pullbackPushforwardAdjunction f)

/-- The affine associated-module/global-sections adjunction applied degreewise to cochain
complexes. -/
noncomputable def affineBaseModuleComplexAdjunction
    (A : Type u) [CommRing A] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of A)) :
    (affineBaseModuleAssociatedFunctor A f).mapHomologicalComplex (up ℤ) ⊣
      (affineBaseModuleGlobalSectionsFunctor A f).mapHomologicalComplex (up ℤ) :=
  let G := affineBaseModuleAssociatedFunctor A f
  let F := affineBaseModuleGlobalSectionsFunctor A f
  let adj := affineBaseModuleAdjunction A f
  let unit : 𝟭 (HomologicalComplex (ModuleCat A) (up ℤ)) ⟶
      G.mapHomologicalComplex (up ℤ) ⋙ F.mapHomologicalComplex (up ℤ) :=
    { app := fun K =>
        { f := fun i => adj.unit.app (K.X i)
          comm' := by
            intro i j hij
            change adj.unit.app (K.X i) ≫ F.map (G.map (K.d i j)) =
              K.d i j ≫ adj.unit.app (K.X j)
            exact (adj.unit.naturality (K.d i j)).symm }
      naturality := by
        intro K L g
        apply HomologicalComplex.hom_ext
        intro i
        exact adj.unit.naturality (g.f i) }
  let counit : F.mapHomologicalComplex (up ℤ) ⋙ G.mapHomologicalComplex (up ℤ) ⟶
      𝟭 (HomologicalComplex X.Modules (up ℤ)) :=
    { app := fun K =>
        { f := fun i => adj.counit.app (K.X i)
          comm' := by
            intro i j hij
            change adj.counit.app (K.X i) ≫ K.d i j =
              G.map (F.map (K.d i j)) ≫ adj.counit.app (K.X j)
            exact (adj.counit.naturality (K.d i j)).symm }
      naturality := by
        intro K L g
        apply HomologicalComplex.hom_ext
        intro i
        exact adj.counit.naturality (g.f i) }
  {
    unit := unit
    counit := counit
    left_triangle_components := by
      intro K
      apply HomologicalComplex.hom_ext
      intro i
      change G.map (adj.unit.app (K.X i)) ≫
        adj.counit.app (G.obj (K.X i)) = 𝟙 _
      exact adj.left_triangle_components (K.X i)
    right_triangle_components := by
      intro K
      apply HomologicalComplex.hom_ext
      intro i
      change adj.unit.app (F.obj (K.X i)) ≫
        F.map (adj.counit.app (K.X i)) = 𝟙 _
      exact adj.right_triangle_components (K.X i) }

/-- The affine associated-module/global-sections adjunction transported to cochain homotopy
categories. -/
noncomputable def affineBaseModuleHomotopyAdjunction
    (A : Type u) [CommRing A] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of A)) :
    (affineBaseModuleAssociatedFunctor A f).mapHomotopyCategory (up ℤ) ⊣
      (affineBaseModuleGlobalSectionsFunctor A f).mapHomotopyCategory (up ℤ) :=
  let G := affineBaseModuleAssociatedFunctor A f
  let F := affineBaseModuleGlobalSectionsFunctor A f
  let adj := affineBaseModuleComplexAdjunction A f
  let unit : 𝟭 (HomotopyCategory (ModuleCat A) (up ℤ)) ⟶
      G.mapHomotopyCategory (up ℤ) ⋙ F.mapHomotopyCategory (up ℤ) :=
    { app := fun K =>
        (HomotopyCategory.quotient (ModuleCat A) (up ℤ)).map (adj.unit.app K.as)
      naturality := by
        rintro ⟨K⟩ ⟨L⟩ ⟨g⟩
        change
          (HomotopyCategory.quotient (ModuleCat A) (up ℤ)).map
              (g ≫ adj.unit.app L) =
            (HomotopyCategory.quotient (ModuleCat A) (up ℤ)).map
              (adj.unit.app K ≫
                (G.mapHomologicalComplex (up ℤ) ⋙
                  F.mapHomologicalComplex (up ℤ)).map g)
        exact congrArg
          (fun k => (HomotopyCategory.quotient (ModuleCat A) (up ℤ)).map k)
          (adj.unit.naturality g) }
  let counit : F.mapHomotopyCategory (up ℤ) ⋙ G.mapHomotopyCategory (up ℤ) ⟶
      𝟭 (HomotopyCategory X.Modules (up ℤ)) :=
    { app := fun K =>
        (HomotopyCategory.quotient X.Modules (up ℤ)).map (adj.counit.app K.as)
      naturality := by
        rintro ⟨K⟩ ⟨L⟩ ⟨g⟩
        change
          (HomotopyCategory.quotient X.Modules (up ℤ)).map
              ((F.mapHomologicalComplex (up ℤ) ⋙
                G.mapHomologicalComplex (up ℤ)).map g ≫ adj.counit.app L) =
            (HomotopyCategory.quotient X.Modules (up ℤ)).map
              (adj.counit.app K ≫ g)
        exact congrArg
          (fun k => (HomotopyCategory.quotient X.Modules (up ℤ)).map k)
          (adj.counit.naturality g) }
  {
    unit := unit
    counit := counit
    left_triangle_components := by
      intro K
      obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective K
      dsimp [unit, counit]
      change
        (HomotopyCategory.quotient X.Modules (up ℤ)).map
              (((affineBaseModuleAssociatedFunctor A f).mapHomologicalComplex (up ℤ)).map
                (adj.unit.app K)) ≫
            (HomotopyCategory.quotient X.Modules (up ℤ)).map
              (adj.counit.app
                (((affineBaseModuleAssociatedFunctor A f).mapHomologicalComplex (up ℤ)).obj K)) =
          𝟙 ((HomotopyCategory.quotient X.Modules (up ℤ)).obj
            (((affineBaseModuleAssociatedFunctor A f).mapHomologicalComplex (up ℤ)).obj K))
      have h := congrArg
        (fun k => (HomotopyCategory.quotient X.Modules (up ℤ)).map k)
        (adj.left_triangle_components K)
      rw [Functor.map_comp] at h
      exact h.trans ((HomotopyCategory.quotient X.Modules (up ℤ)).map_id _)
    right_triangle_components := by
      intro K
      obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective K
      dsimp [unit, counit]
      change
        (HomotopyCategory.quotient (ModuleCat A) (up ℤ)).map
              (adj.unit.app
                (((affineBaseModuleGlobalSectionsFunctor A f).mapHomologicalComplex (up ℤ)).obj K)) ≫
            (HomotopyCategory.quotient (ModuleCat A) (up ℤ)).map
              (((affineBaseModuleGlobalSectionsFunctor A f).mapHomologicalComplex (up ℤ)).map
                (adj.counit.app K)) =
          𝟙 ((HomotopyCategory.quotient (ModuleCat A) (up ℤ)).obj
            (((affineBaseModuleGlobalSectionsFunctor A f).mapHomologicalComplex (up ℤ)).obj K))
      have h := congrArg
        (fun k => (HomotopyCategory.quotient (ModuleCat A) (up ℤ)).map k)
        (adj.right_triangle_components K)
      rw [Functor.map_comp] at h
      exact h.trans ((HomotopyCategory.quotient (ModuleCat A) (up ℤ)).map_id _) }

namespace AffineBaseModuleDerivedAdjunction

/-- The affine associated-module functor admits its standard total left derived functor. -/
abbrev HasLeftDerived
    (A : Type u) [CommRing A] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of A)) : Prop :=
  (@Functor.Homotopy.toDerived
    (ModuleCat A) inferInstance inferInstance
    X.Modules inferInstance inferInstance (HasDerivedCategory.standard X.Modules)
    (affineBaseModuleAssociatedFunctor A f)
    (affineBaseModuleAssociatedFunctorAdditive A f)).HasLeftDerivedFunctor
      (HomotopyCategory.quasiIso (ModuleCat A) (up ℤ))

/-- Affine-base global sections have their standard total right derived functor. -/
abbrev HasRightDerived
    (A : Type u) [CommRing A] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of A)) : Prop :=
  (@Functor.Homotopy.toDerived
    X.Modules inferInstance inferInstance
    (ModuleCat A) inferInstance inferInstance inferInstance
    (affineBaseModuleGlobalSectionsFunctor A f)
    (affineBaseModuleGlobalSectionsFunctorAdditive A f)).HasRightDerivedFunctor
      (HomotopyCategory.quasiIso X.Modules (up ℤ))

/-- The two absolute-derived conditions needed for the affine derived adjunction. -/
abbrev HasPair
    (A : Type u) [CommRing A] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of A))
    [hLeft : (Functor.Homotopy.toDerived
      (affineBaseModuleAssociatedFunctor A f)).HasLeftDerivedFunctor
        (HomotopyCategory.quasiIso (ModuleCat A) (up ℤ))]
    [hRight : (Functor.Homotopy.toDerived
      (affineBaseModuleGlobalSectionsFunctor A f)).HasRightDerivedFunctor
        (HomotopyCategory.quasiIso X.Modules (up ℤ))] : Prop :=
  @CategoryTheory.Adjunction.TotalDerived.HasPair
    (HomotopyCategory (ModuleCat A) (up ℤ))
    (HomotopyCategory X.Modules (up ℤ))
    (DerivedCategory (ModuleCat A)) (DerivedCategory X.Modules)
    inferInstance inferInstance inferInstance inferInstance
    ((affineBaseModuleAssociatedFunctor A f).mapHomotopyCategory (up ℤ))
    ((affineBaseModuleGlobalSectionsFunctor A f).mapHomotopyCategory (up ℤ))
    (HomotopyCategory.quasiIso (ModuleCat A) (up ℤ))
    (HomotopyCategory.quasiIso X.Modules (up ℤ))
    DerivedCategory.Qh DerivedCategory.Qh inferInstance inferInstance hLeft hRight

end AffineBaseModuleDerivedAdjunction

/-- The standard total left-derived affine associated-module functor. -/
abbrev affineBaseModuleDerivedAssociatedFunctor
    (A : Type u) [CommRing A] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of A))
    [AffineBaseModuleDerivedAdjunction.HasLeftDerived A f] :
    DerivedCategory (ModuleCat A) ⥤ DerivedCategory X.Modules :=
  Functor.LeftDerived.Homotopy.functor (affineBaseModuleAssociatedFunctor A f)

/-- The standard total right-derived global-sections functor relative to an affine base. -/
abbrev affineBaseModuleDerivedGlobalSectionsFunctor
    (A : Type u) [CommRing A] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of A))
    [AffineBaseModuleDerivedAdjunction.HasRightDerived A f] :
    DerivedCategory X.Modules ⥤ DerivedCategory (ModuleCat A) :=
  Functor.RightDerived.Homotopy.functor (affineBaseModuleGlobalSectionsFunctor A f)

/-- The canonical adjunction between the standard affine derived functors. -/
noncomputable def affineBaseModuleDerivedAdjunction
    (A : Type u) [CommRing A] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of A))
    [hLeft : AffineBaseModuleDerivedAdjunction.HasLeftDerived A f]
    [hRight : AffineBaseModuleDerivedAdjunction.HasRightDerived A f]
    [hPair : AffineBaseModuleDerivedAdjunction.HasPair A f] :
    affineBaseModuleDerivedAssociatedFunctor A f ⊣
      affineBaseModuleDerivedGlobalSectionsFunctor A f :=
  @CategoryTheory.Adjunction.TotalDerived.HasPair.derived
    (HomotopyCategory (ModuleCat A) (up ℤ))
    (HomotopyCategory X.Modules (up ℤ))
    (DerivedCategory (ModuleCat A)) (DerivedCategory X.Modules)
    inferInstance inferInstance inferInstance inferInstance
    ((affineBaseModuleAssociatedFunctor A f).mapHomotopyCategory (up ℤ))
    ((affineBaseModuleGlobalSectionsFunctor A f).mapHomotopyCategory (up ℤ))
    (affineBaseModuleHomotopyAdjunction A f)
    (HomotopyCategory.quasiIso (ModuleCat A) (up ℤ))
    (HomotopyCategory.quasiIso X.Modules (up ℤ))
    DerivedCategory.Qh DerivedCategory.Qh inferInstance inferInstance hLeft hRight hPair

/-- The derived global-sections object of a module relative to an affine base. -/
abbrev affineBaseModuleDerivedGlobalSections
    (A : Type u) [CommRing A] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of A))
    [AffineBaseModuleDerivedAdjunction.HasRightDerived A f]
    (ℱ : X.Modules) : DerivedCategory (ModuleCat A) :=
  (affineBaseModuleDerivedGlobalSectionsFunctor A f).obj
    ((DerivedCategory.singleFunctor X.Modules 0).obj ℱ)

/-- The derived global-sections object after affine base change. -/
abbrev affineBaseChangedModuleDerivedGlobalSections
    (A A' : Type u) [CommRing A] [CommRing A'] [Algebra A A']
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A))
    [AffineBaseModuleDerivedAdjunction.HasRightDerived A'
      (Scheme.AffineBaseChange.toBase A A' f)]
    (ℱ : X.Modules) : DerivedCategory (ModuleCat A') :=
  affineBaseModuleDerivedGlobalSections A'
    (Scheme.AffineBaseChange.toBase A A' f)
    (Scheme.Modules.AffineBaseChange.baseChange A A' f ℱ)

namespace AffineBaseChangeDerivedCompatibility

/-- Derived scalar extension exists for the selected map of affine bases. -/
abbrev HasScalarExtension
    (A A' : Type u) [CommRing A] [CommRing A'] [Algebra A A'] : Prop :=
  (ModuleCat.extendScalarsToDerived.{u, u, u}
    (algebraMap A A')).HasLeftDerivedFunctor
      (HomotopyCategory.quasiIso (ModuleCat.{u} A) (up ℤ))

/-- Pullback along the projection from an affine base change admits its total left derived
functor. -/
abbrev HasPullback
    (A A' : Type u) [CommRing A] [CommRing A'] [Algebra A A']
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A)) : Prop :=
  (@Functor.Homotopy.toDerived
    X.Modules inferInstance inferInstance
    (Scheme.AffineBaseChange.baseChange A A' f).Modules inferInstance inferInstance
      (HasDerivedCategory.standard
        (Scheme.AffineBaseChange.baseChange A A' f).Modules)
    (Scheme.Modules.pullback (Scheme.AffineBaseChange.toSource A A' f))
    inferInstance).HasLeftDerivedFunctor
      (HomotopyCategory.quasiIso X.Modules (up ℤ))

/-- The scalar-extension-first iterated functor has the universal property of the derived
composite. -/
abbrev SourceRoute
    (A A' : Type u) [CommRing A] [CommRing A'] [Algebra A A']
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A))
    [HasScalarExtension A A']
    [AffineBaseModuleDerivedAdjunction.HasLeftDerived A'
      (Scheme.AffineBaseChange.toBase A A' f)] : Prop :=
  (ModuleCat.derivedExtensionOfScalars (algebraMap A A') ⋙
      affineBaseModuleDerivedAssociatedFunctor A'
        (Scheme.AffineBaseChange.toBase A A' f)).IsLeftDerivedFunctor
    (Functor.LeftDerived.Homotopy.Composition.counit
      (affineBaseModuleAssociatedFunctor A'
        (Scheme.AffineBaseChange.toBase A A' f))
      (ModuleCat.extendScalars (algebraMap A A')))
    (HomotopyCategory.quasiIso (ModuleCat A) (up ℤ))

/-- The associated-module-first iterated functor has the universal property of the derived
composite. -/
abbrev TargetRoute
    (A A' : Type u) [CommRing A] [CommRing A'] [Algebra A A']
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A))
    [AffineBaseModuleDerivedAdjunction.HasLeftDerived A f]
    [HasPullback A A' f] : Prop :=
  (affineBaseModuleDerivedAssociatedFunctor A f ⋙
      Functor.LeftDerived.Homotopy.functor
        (Scheme.Modules.pullback
          (Scheme.AffineBaseChange.toSource A A' f))).IsLeftDerivedFunctor
    (Functor.LeftDerived.Homotopy.Composition.counit
      (Scheme.Modules.pullback (Scheme.AffineBaseChange.toSource A A' f))
      (affineBaseModuleAssociatedFunctor A f))
    (HomotopyCategory.quasiIso (ModuleCat A) (up ℤ))

end AffineBaseChangeDerivedCompatibility

/-- The standard total left-derived pullback along the projection from an affine base change. -/
abbrev affineBaseChangeModuleDerivedPullbackFunctor
    (A A' : Type u) [CommRing A] [CommRing A'] [Algebra A A']
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A))
    [AffineBaseChangeDerivedCompatibility.HasPullback A A' f] :
    DerivedCategory X.Modules ⥤
      DerivedCategory (Scheme.AffineBaseChange.baseChange A A' f).Modules :=
  Functor.LeftDerived.Homotopy.functor
    (Scheme.Modules.pullback (Scheme.AffineBaseChange.toSource A A' f))

/-- Extension of scalars followed by affine associated-module formation is canonically the same
as affine associated-module formation followed by pullback to the changed base. -/
noncomputable def affineBaseModulePullbackSquare
    (A A' : Type u) [CommRing A] [CommRing A'] [Algebra A A']
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A)) :
    ModuleCat.extendScalars (algebraMap A A') ⋙
        affineBaseModuleAssociatedFunctor A'
          (Scheme.AffineBaseChange.toBase A A' f) ≅
      affineBaseModuleAssociatedFunctor A f ⋙
        Scheme.Modules.pullback (Scheme.AffineBaseChange.toSource A A' f) :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (tilde.ChangeOfRings.Pullback.iso
        (CommRingCat.ofHom (algebraMap A A'))).symm _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _
      (Scheme.Modules.pullbackComp
        (Scheme.AffineBaseChange.toBase A A' f)
        (Scheme.AffineBaseChange.specMap A A')) ≪≫
    Functor.isoWhiskerLeft _
      (Scheme.Modules.pullbackCongr
        (Limits.pullback.condition (f := f)
          (g := Scheme.AffineBaseChange.specMap A A')).symm) ≪≫
    Functor.isoWhiskerLeft _
      (Scheme.Modules.pullbackComp
        (Scheme.AffineBaseChange.toSource A A' f) f).symm ≪≫
    (Functor.associator _ _ _).symm

/-- The two canonical iterated total-left-derived routes form the derived affine pullback
square. -/
noncomputable def affineBaseModuleDerivedPullbackSquare
    (A A' : Type u) [CommRing A] [CommRing A'] [Algebra A A']
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A))
    [AffineBaseModuleDerivedAdjunction.HasLeftDerived A f]
    [AffineBaseModuleDerivedAdjunction.HasLeftDerived A'
      (Scheme.AffineBaseChange.toBase A A' f)]
    [AffineBaseChangeDerivedCompatibility.HasScalarExtension A A']
    [AffineBaseChangeDerivedCompatibility.HasPullback A A' f]
    [AffineBaseChangeDerivedCompatibility.SourceRoute A A' f]
    [AffineBaseChangeDerivedCompatibility.TargetRoute A A' f] :
    ModuleCat.derivedExtensionOfScalars (algebraMap A A') ⋙
        affineBaseModuleDerivedAssociatedFunctor A'
          (Scheme.AffineBaseChange.toBase A A' f) ≅
      affineBaseModuleDerivedAssociatedFunctor A f ⋙
        affineBaseChangeModuleDerivedPullbackFunctor A A' f :=
  Functor.leftDerivedNatIso
    (ModuleCat.derivedExtensionOfScalars (algebraMap A A') ⋙
      affineBaseModuleDerivedAssociatedFunctor A'
        (Scheme.AffineBaseChange.toBase A A' f))
    (affineBaseModuleDerivedAssociatedFunctor A f ⋙
      affineBaseChangeModuleDerivedPullbackFunctor A A' f)
    (Functor.LeftDerived.Homotopy.Composition.counit
      (affineBaseModuleAssociatedFunctor A'
        (Scheme.AffineBaseChange.toBase A A' f))
      (ModuleCat.extendScalars (algebraMap A A')))
    (Functor.LeftDerived.Homotopy.Composition.counit
      (Scheme.Modules.pullback (Scheme.AffineBaseChange.toSource A A' f))
      (affineBaseModuleAssociatedFunctor A f))
    (HomotopyCategory.quasiIso (ModuleCat A) (up ℤ))
    ((Functor.LeftDerived.Homotopy.Composition.toDerivedIso
      (affineBaseModuleAssociatedFunctor A'
        (Scheme.AffineBaseChange.toBase A A' f))
      (ModuleCat.extendScalars (algebraMap A A'))
      (ModuleCat.extendScalars (algebraMap A A') ⋙
        affineBaseModuleAssociatedFunctor A'
          (Scheme.AffineBaseChange.toBase A A' f))
      (Iso.refl _)).symm ≪≫
    Functor.isoWhiskerRight
      (Functor.mapHomotopyCategoryIso (affineBaseModulePullbackSquare A A' f))
      (DerivedCategory.Qh :
        HomotopyCategory (Scheme.AffineBaseChange.baseChange A A' f).Modules (up ℤ) ⥤
          DerivedCategory (Scheme.AffineBaseChange.baseChange A A' f).Modules) ≪≫
    Functor.LeftDerived.Homotopy.Composition.toDerivedIso
      (Scheme.Modules.pullback (Scheme.AffineBaseChange.toSource A A' f))
      (affineBaseModuleAssociatedFunctor A f)
      (affineBaseModuleAssociatedFunctor A f ⋙
        Scheme.Modules.pullback (Scheme.AffineBaseChange.toSource A A' f))
      (Iso.refl _))

/-- The canonical derived affine base-change map, obtained as the right mate of the derived
pullback square and evaluated on a module in degree zero. -/
noncomputable def affineBaseModuleDerivedGlobalSectionsBaseChangeMap
    (A A' : Type u) [CommRing A] [CommRing A'] [Algebra A A']
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A))
    [AffineBaseModuleDerivedAdjunction.HasLeftDerived A f]
    [AffineBaseModuleDerivedAdjunction.HasRightDerived A f]
    [AffineBaseModuleDerivedAdjunction.HasPair A f]
    [AffineBaseModuleDerivedAdjunction.HasLeftDerived A'
      (Scheme.AffineBaseChange.toBase A A' f)]
    [AffineBaseModuleDerivedAdjunction.HasRightDerived A'
      (Scheme.AffineBaseChange.toBase A A' f)]
    [AffineBaseModuleDerivedAdjunction.HasPair A'
      (Scheme.AffineBaseChange.toBase A A' f)]
    [AffineBaseChangeDerivedCompatibility.HasScalarExtension A A']
    [AffineBaseChangeDerivedCompatibility.HasPullback A A' f]
    [AffineBaseChangeDerivedCompatibility.SourceRoute A A' f]
    [AffineBaseChangeDerivedCompatibility.TargetRoute A A' f]
    (ℱ : X.Modules) :
    (ModuleCat.derivedExtensionOfScalars (algebraMap A A')).obj
        (affineBaseModuleDerivedGlobalSections A f ℱ) ⟶
      affineBaseChangedModuleDerivedGlobalSections A A' f ℱ := by
  let K := (HomotopyCategory.singleFunctor X.Modules 0).obj ℱ
  let mate := CategoryTheory.DerivedBaseChange.app
    (affineBaseModuleDerivedAdjunction A f)
    (affineBaseModuleDerivedAdjunction A'
      (Scheme.AffineBaseChange.toBase A A' f))
    (affineBaseModuleDerivedPullbackSquare A A' f)
    ((DerivedCategory.Qh : HomotopyCategory X.Modules (up ℤ) ⥤
      DerivedCategory X.Modules).obj K)
  let singleIso :
      (Functor.Homotopy.toDerived
        (Scheme.Modules.pullback
          (Scheme.AffineBaseChange.toSource A A' f))).obj K ≅
        (DerivedCategory.singleFunctor
          (Scheme.AffineBaseChange.baseChange A A' f).Modules 0).obj
            (Scheme.Modules.AffineBaseChange.baseChange A A' f ℱ) :=
    (DerivedCategory.Qh :
      HomotopyCategory (Scheme.AffineBaseChange.baseChange A A' f).Modules (up ℤ) ⥤
        DerivedCategory (Scheme.AffineBaseChange.baseChange A A' f).Modules).mapIso
      ((HomotopyCategory.quotient
        (Scheme.AffineBaseChange.baseChange A A' f).Modules (up ℤ)).mapIso
          ((HomologicalComplex.singleMapHomologicalComplex
            (Scheme.Modules.pullback (Scheme.AffineBaseChange.toSource A A' f))
            (up ℤ) 0).app ℱ))
  let comparison :=
    (affineBaseModuleDerivedGlobalSectionsFunctor A'
      (Scheme.AffineBaseChange.toBase A A' f)).map
      ((Functor.LeftDerived.Homotopy.counit
        (Scheme.Modules.pullback
          (Scheme.AffineBaseChange.toSource A A' f))).app K ≫ singleIso.hom)
  exact mate ≫ comparison

end AlgebraicGeometry.Scheme.Modules
