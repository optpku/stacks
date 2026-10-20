module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import ReasLib.AlgebraicGeometry.RingedSite.Simplicial.Morphism
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.Module.Derived.Pushforward
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.Module.Pullback.Complex
public import ReasLib.CategoryTheory.Functor.Derived.Composition.Right

/-!
# Derived direct image and restriction on ringed simplicial sites

Exact restriction to a stage commutes with the unbounded derived direct image
of modules, for covariant and fiberwise simplicial sites.
-/

@[expose] public section

universe u v w

open CategoryTheory CategoryTheory.Limits Opposite ComplexShape
open RingedSite RingedSite.ToposHom
open scoped MorphismOfTopoiIn

noncomputable section

namespace CategoryTheory.SimplicialSites

variable (C : SimplexCategory ⥤ Cat.{v, u})
variable (J : ∀ n, Precoverage (C.obj n))
variable [∀ n, HasWeakSheafify (J n).toGrothendieck (Type w)]
variable [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (C.obj m)ᵒᵖ ⥤ Type w),
    ((C.map φ).toFunctor).op.HasLeftKanExtension P]
variable [IsMorphismDiagram C J]
variable [HasWeakSheafify (topology C J) (Type w)]
variable (O : Sheaf (topology C J) RingCat.{w})
variable [(topology C J).HasSheafCompose (forget RingCat.{w})]
variable [∀ n, ((J n).toGrothendieck).HasSheafCompose (forget RingCat.{w})]
variable [∀ n, HasSheafify ((J n).toGrothendieck) (Type w)]
variable [HasSheafify (topology C J) (Type w)]
variable [∀ n, ∀ P : (C.obj n)ᵒᵖ ⥤ Type w, (ofStage C n).op.HasLeftKanExtension P]
variable [∀ n, ∀ P : (C.obj n)ᵒᵖ ⥤ Type w, (ofStage C n).op.HasPointwiseRightKanExtension P]
variable [∀ n, (SheafOfModules.restrictScalars.{w}
    (stageMorphism C J O n).structureMap).IsRightAdjoint]
variable [UnivLE.{max u v, w}]

/-- Pullback from the total ringed site to a stage preserves finite limits. -/
instance stageMorphism_modulePullback_preservesFiniteLimits (n : SimplexCategory) :
    PreservesFiniteLimits (stageMorphism C J O n).modulePullback :=
  sorry

/-- Pullback from the total ringed site to a stage preserves finite colimits. -/
instance stageMorphism_modulePullback_preservesFiniteColimits (n : SimplexCategory) :
    PreservesFiniteColimits (stageMorphism C J O n).modulePullback :=
  sorry

/-- Exact restriction of unbounded derived modules from the total site to a stage. -/
def derivedModuleRestrict (n : SimplexCategory) :
    Hom.ModuleDerived.{w} (totalRingedSite C J O) ⥤
      Hom.ModuleDerived.{w} (componentRingedSite C J O n) :=
  @Functor.mapDerivedCategory _ _ _ (Hom.moduleCat_hasDerivedCategory (totalRingedSite C J O))
    _ _ _ (Hom.moduleCat_hasDerivedCategory (componentRingedSite C J O n))
    (stageMorphism C J O n).modulePullback
    (modulePullback_additive (stageMorphism C J O n)) inferInstance inferInstance

/-- Derived restriction is induced by termwise restriction of cochain complexes. -/
def derivedModuleRestrict_factors (n : SimplexCategory) :
    (@DerivedCategory.Q _ _ _ (Hom.moduleCat_hasDerivedCategory (totalRingedSite C J O))) ⋙ derivedModuleRestrict C J O n ≅
      (stageMorphism C J O n).modulePullbackComplex ⋙
        (@DerivedCategory.Q _ _ _ (Hom.moduleCat_hasDerivedCategory (componentRingedSite C J O n))) :=
  @Functor.mapDerivedCategoryFactors _ _ _ (Hom.moduleCat_hasDerivedCategory (totalRingedSite C J O))
    _ _ _ (Hom.moduleCat_hasDerivedCategory (componentRingedSite C J O n))
    (stageMorphism C J O n).modulePullback
    (modulePullback_additive (stageMorphism C J O n)) inferInstance inferInstance

end CategoryTheory.SimplicialSites

namespace CategoryTheory.SimplicialSites

variable {C C' : SimplexCategory ⥤ Cat.{v, u}}
variable (J : ∀ n, Precoverage (C.obj n)) (J' : ∀ n, Precoverage (C'.obj n))
variable [∀ n, HasWeakSheafify (J n).toGrothendieck (Type w)]
variable [∀ n, HasWeakSheafify (J' n).toGrothendieck (Type w)]
variable [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (C.obj m)ᵒᵖ ⥤ Type w),
    ((C.map φ).toFunctor).op.HasLeftKanExtension P]
variable [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (C'.obj m)ᵒᵖ ⥤ Type w),
    ((C'.map φ).toFunctor).op.HasLeftKanExtension P]
variable [IsMorphismDiagram C J] [IsMorphismDiagram C' J']
variable [HasWeakSheafify (topology C J) (Type w)]
variable [HasWeakSheafify (topology C' J') (Type w)]
variable (O : Sheaf (topology C J) RingCat.{w})
variable (O' : Sheaf (topology C' J') RingCat.{w})
variable [(topology C J).HasSheafCompose (forget RingCat.{w})]
variable [(topology C' J').HasSheafCompose (forget RingCat.{w})]
variable [∀ n, ((J n).toGrothendieck).HasSheafCompose (forget RingCat.{w})]
variable [∀ n, ((J' n).toGrothendieck).HasSheafCompose (forget RingCat.{w})]
variable [∀ n, HasSheafify ((J n).toGrothendieck) (Type w)]
variable [∀ n, HasSheafify ((J' n).toGrothendieck) (Type w)]
variable [HasSheafify (topology C J) (Type w)]
variable [HasSheafify (topology C' J') (Type w)]
variable [∀ n, ∀ P : (C.obj n)ᵒᵖ ⥤ Type w, (ofStage C n).op.HasLeftKanExtension P]
variable [∀ n, ∀ P : (C'.obj n)ᵒᵖ ⥤ Type w, (ofStage C' n).op.HasLeftKanExtension P]
variable [∀ n, ∀ P : (C.obj n)ᵒᵖ ⥤ Type w, (ofStage C n).op.HasPointwiseRightKanExtension P]
variable [∀ n, ∀ P : (C'.obj n)ᵒᵖ ⥤ Type w, (ofStage C' n).op.HasPointwiseRightKanExtension P]

namespace RingedMorphism

variable {J J' O O'}
variable (f : RingedMorphism J J' O O')
variable [∀ n (P : (C'.obj n)ᵒᵖ ⥤ Type w),
    ((f.toSimplicial.app n).toFunctor).op.HasLeftKanExtension P]
variable [∀ P : (totalSite C')ᵒᵖ ⥤ Type w,
    (IsMorphism.totalFunctor f.toSimplicial).op.HasLeftKanExtension P]
variable [∀ n, (SheafOfModules.restrictScalars.{w}
    (stageMorphism C J O n).structureMap).IsRightAdjoint]
variable [∀ n, (SheafOfModules.restrictScalars.{w}
    (stageMorphism C' J' O' n).structureMap).IsRightAdjoint]
variable [UnivLE.{max u v, w}]
variable [hTotal : HasModulePushforwardDerived (toToposHom f)]
variable [hComponent : ∀ n, HasModulePushforwardDerived (topos f n)]

/-- Cochain restriction of total module direct image is naturally isomorphic to
component direct image of cochain restriction. -/
def restrict_modulePushforward_cochain (n : SimplexCategory) :
    (@Functor.mapHomologicalComplex _ _ _ _ _ _ _ (toToposHom f).modulePushforward
      (@Functor.preservesZeroMorphisms_of_additive _ _ _ _ _ _ _
        (modulePushforward_additive (toToposHom f))) (up ℤ)) ⋙
        (stageMorphism C' J' O' n).modulePullbackComplex ≅
      (stageMorphism C J O n).modulePullbackComplex ⋙
        (@Functor.mapHomologicalComplex _ _ _ _ _ _ _ (topos f n).modulePushforward
      (@Functor.preservesZeroMorphisms_of_additive _ _ _ _ _ _ _
        (modulePushforward_additive (topos f n))) (up ℤ)) :=
  @NatIso.mapHomologicalComplex _ _ _ _ _ _ _ _ _
    (@Functor.preservesZeroMorphisms_comp _ _ _ _ _ _ _ _ _
      (toToposHom f).modulePushforward (stageMorphism C' J' O' n).modulePullback
      (@Functor.preservesZeroMorphisms_of_additive _ _ _ _ _ _ _
          (modulePushforward_additive (toToposHom f)))
      (@Functor.preservesZeroMorphisms_of_additive _ _ _ _ _ _ _
          (modulePullback_additive (stageMorphism C' J' O' n))))
    (@Functor.preservesZeroMorphisms_comp _ _ _ _ _ _ _ _ _
      (stageMorphism C J O n).modulePullback (topos f n).modulePushforward
      (@Functor.preservesZeroMorphisms_of_additive _ _ _ _ _ _ _
          (modulePullback_additive (stageMorphism C J O n)))
      (@Functor.preservesZeroMorphisms_of_additive _ _ _ _ _ _ _
          (modulePushforward_additive (topos f n))))
    (restrict_modulePushforward f n) (up ℤ)

/-- Restriction of derived total module direct image is a right derived functor
of the mixed cochain composite. -/
theorem restrict_modulePushforwardDerived_isRightDerived (n : SimplexCategory) :
    (modulePushforwardDerived (toToposHom f) ⋙ derivedModuleRestrict C' J' O' n).IsRightDerivedFunctor
      ((Functor.associator
            ((stageMorphism C J O n).modulePullbackComplex)
            ((@Functor.mapHomologicalComplex _ _ _ _ _ _ _ (topos f n).modulePushforward
      (@Functor.preservesZeroMorphisms_of_additive _ _ _ _ _ _ _
        (modulePushforward_additive (topos f n))) (up ℤ)))
            ((@DerivedCategory.Q _ _ _ (Hom.moduleCat_hasDerivedCategory (componentRingedSite C' J' O' n))))).inv ≫
        Functor.whiskerRight (restrict_modulePushforward_cochain f n).inv
          ((@DerivedCategory.Q _ _ _ (Hom.moduleCat_hasDerivedCategory (componentRingedSite C' J' O' n)))) ≫
          (Functor.associator
                ((@Functor.mapHomologicalComplex _ _ _ _ _ _ _ (toToposHom f).modulePushforward
      (@Functor.preservesZeroMorphisms_of_additive _ _ _ _ _ _ _
        (modulePushforward_additive (toToposHom f))) (up ℤ)))
                ((stageMorphism C' J' O' n).modulePullbackComplex)
                ((@DerivedCategory.Q _ _ _ (Hom.moduleCat_hasDerivedCategory (componentRingedSite C' J' O' n))))).hom ≫
            Functor.RightDerived.Composition.iteratedUnit
              ((@Functor.RightDerived.Homotopy.cochainUnit _ _ _ (Hom.moduleCat_hasDerivedCategory _)
      _ _ _ (Hom.moduleCat_hasDerivedCategory _) (toToposHom f).modulePushforward
      (modulePushforward_additive (toToposHom f)) hTotal))
              (derivedModuleRestrict_factors C' J' O' n).inv)
      (HomologicalComplex.quasiIso (SheafOfModules.{w} O) (up ℤ)) :=
  sorry

/-- The canonical comparison from restriction of derived total direct image to
derived component direct image of restriction. -/
def restrict_modulePushforwardDerived_hom (n : SimplexCategory) :
    modulePushforwardDerived (toToposHom f) ⋙ derivedModuleRestrict C' J' O' n ⟶
      derivedModuleRestrict C J O n ⋙ modulePushforwardDerived (topos f n) :=
  Functor.RightDerived.Composition.squareOfIso
    (hαGF := restrict_modulePushforwardDerived_isRightDerived f n)
    (HomologicalComplex.quasiIso (SheafOfModules.{w} O) (up ℤ))
    (restrict_modulePushforward_cochain f n)
    ((@Functor.RightDerived.Homotopy.cochainUnit _ _ _ (Hom.moduleCat_hasDerivedCategory _)
      _ _ _ (Hom.moduleCat_hasDerivedCategory _) (toToposHom f).modulePushforward
      (modulePushforward_additive (toToposHom f)) hTotal))
    (derivedModuleRestrict_factors C' J' O' n).inv
    (derivedModuleRestrict_factors C J O n).inv
    ((@Functor.RightDerived.Homotopy.cochainUnit _ _ _ (Hom.moduleCat_hasDerivedCategory _)
      _ _ _ (Hom.moduleCat_hasDerivedCategory _) (topos f n).modulePushforward
      (modulePushforward_additive (topos f n)) (hComponent n)))

/-- The canonical derived comparison factors the transported cochain unit through
restriction followed by component direct image. -/
theorem restrict_modulePushforwardDerived_hom_fac (n : SimplexCategory) :
    ((Functor.associator
            ((stageMorphism C J O n).modulePullbackComplex)
            ((@Functor.mapHomologicalComplex _ _ _ _ _ _ _ (topos f n).modulePushforward
      (@Functor.preservesZeroMorphisms_of_additive _ _ _ _ _ _ _
        (modulePushforward_additive (topos f n))) (up ℤ)))
            ((@DerivedCategory.Q _ _ _ (Hom.moduleCat_hasDerivedCategory (componentRingedSite C' J' O' n))))).inv ≫
        Functor.whiskerRight (restrict_modulePushforward_cochain f n).inv
          ((@DerivedCategory.Q _ _ _ (Hom.moduleCat_hasDerivedCategory (componentRingedSite C' J' O' n)))) ≫
          (Functor.associator
                ((@Functor.mapHomologicalComplex _ _ _ _ _ _ _ (toToposHom f).modulePushforward
      (@Functor.preservesZeroMorphisms_of_additive _ _ _ _ _ _ _
        (modulePushforward_additive (toToposHom f))) (up ℤ)))
                ((stageMorphism C' J' O' n).modulePullbackComplex)
                ((@DerivedCategory.Q _ _ _ (Hom.moduleCat_hasDerivedCategory (componentRingedSite C' J' O' n))))).hom ≫
            Functor.RightDerived.Composition.iteratedUnit
              ((@Functor.RightDerived.Homotopy.cochainUnit _ _ _ (Hom.moduleCat_hasDerivedCategory _)
      _ _ _ (Hom.moduleCat_hasDerivedCategory _) (toToposHom f).modulePushforward
      (modulePushforward_additive (toToposHom f)) hTotal))
              (derivedModuleRestrict_factors C' J' O' n).inv) ≫
      Functor.whiskerLeft ((@DerivedCategory.Q _ _ _ (Hom.moduleCat_hasDerivedCategory (totalRingedSite C J O))))
        (restrict_modulePushforwardDerived_hom f n) =
      Functor.RightDerived.Composition.iteratedUnit
        (derivedModuleRestrict_factors C J O n).inv
        ((@Functor.RightDerived.Homotopy.cochainUnit _ _ _ (Hom.moduleCat_hasDerivedCategory _)
      _ _ _ (Hom.moduleCat_hasDerivedCategory _) (topos f n).modulePushforward
      (modulePushforward_additive (topos f n)) (hComponent n))) :=
  sorry

/-- The derived mixed comparison is invertible. -/
instance restrict_modulePushforwardDerived_hom_isIso (n : SimplexCategory) :
    IsIso (restrict_modulePushforwardDerived_hom f n) :=
  sorry

/-- The canonical comparison between restriction of derived total direct image and
derived component direct image of restriction, evaluated at an unbounded derived module. -/
def restrict_modulePushforwardDerived_obj (n : SimplexCategory)
    (K : Hom.ModuleDerived.{w} (totalRingedSite C J O)) :
    (derivedModuleRestrict C' J' O' n).obj ((modulePushforwardDerived (toToposHom f)).obj K) ⟶
      (modulePushforwardDerived (topos f n)).obj ((derivedModuleRestrict C J O n).obj K) :=
  (restrict_modulePushforwardDerived_hom f n).app K

/-- The objectwise mixed comparison is invertible. -/
theorem restrict_modulePushforwardDerived_obj_isIso (n : SimplexCategory)
    (K : Hom.ModuleDerived.{w} (totalRingedSite C J O)) :
    IsIso (restrict_modulePushforwardDerived_obj f n K) :=
  sorry

end RingedMorphism

end CategoryTheory.SimplicialSites

namespace CategoryTheory.Grothendieck

variable (F : SimplicialObject Cat.{v, u})
variable (J : ∀ n, Precoverage (F.obj n))
variable [IsFiberwiseSite F J]
variable [∀ n, HasSheafify (J n).toGrothendieck (Type w)]
variable [HasSheafify (topology F J) (Type w)]
variable [HasWeakSheafify (topology F J) (Type w)]
variable [∀ n, HasWeakSheafify (J n).toGrothendieck (Type w)]
variable (O : Sheaf (topology F J) RingCat.{w})
variable [(topology F J).HasSheafCompose (CategoryTheory.forget RingCat.{w})]
variable [∀ n, ((J n).toGrothendieck).HasSheafCompose (CategoryTheory.forget RingCat.{w})]
variable [∀ n, ∀ P : (F.obj (op n))ᵒᵖ ⥤ Type w,
    (ι F (op n)).op.HasLeftKanExtension P]
variable [∀ n, ∀ P : (F.obj (op n))ᵒᵖ ⥤ Type w,
    (ι F (op n)).op.HasPointwiseRightKanExtension P]
variable [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (F.obj (op n))ᵒᵖ ⥤ Type w),
    ((F.map φ.op).toFunctor).op.HasPointwiseRightKanExtension P]
variable [∀ n, (SheafOfModules.restrictScalars.{w}
    (fiberStageMorphism F J O n).structureMap).IsRightAdjoint]
variable [UnivLE.{max u v, w}]

/-- Pullback from the total ringed site to a stage preserves finite limits. -/
instance fiberStageMorphism_modulePullback_preservesFiniteLimits (n : SimplexCategory) :
    PreservesFiniteLimits (fiberStageMorphism F J O n).modulePullback :=
  sorry

/-- Pullback from the total ringed site to a stage preserves finite colimits. -/
instance fiberStageMorphism_modulePullback_preservesFiniteColimits (n : SimplexCategory) :
    PreservesFiniteColimits (fiberStageMorphism F J O n).modulePullback :=
  sorry

/-- Exact restriction of unbounded derived modules from the total site to a stage. -/
def derivedModuleRestrict (n : SimplexCategory) :
    Hom.ModuleDerived.{w} (fiberTotalRingedSite F J O) ⥤
      Hom.ModuleDerived.{w} (fiberComponentRingedSite F J O n) :=
  @Functor.mapDerivedCategory _ _ _ (Hom.moduleCat_hasDerivedCategory (fiberTotalRingedSite F J O))
    _ _ _ (Hom.moduleCat_hasDerivedCategory (fiberComponentRingedSite F J O n))
    (fiberStageMorphism F J O n).modulePullback
    (modulePullback_additive (fiberStageMorphism F J O n)) inferInstance inferInstance

/-- Derived restriction is induced by termwise restriction of cochain complexes. -/
def derivedModuleRestrict_factors (n : SimplexCategory) :
    (@DerivedCategory.Q _ _ _ (Hom.moduleCat_hasDerivedCategory (fiberTotalRingedSite F J O))) ⋙ derivedModuleRestrict F J O n ≅
      (fiberStageMorphism F J O n).modulePullbackComplex ⋙
        (@DerivedCategory.Q _ _ _ (Hom.moduleCat_hasDerivedCategory (fiberComponentRingedSite F J O n))) :=
  @Functor.mapDerivedCategoryFactors _ _ _ (Hom.moduleCat_hasDerivedCategory (fiberTotalRingedSite F J O))
    _ _ _ (Hom.moduleCat_hasDerivedCategory (fiberComponentRingedSite F J O n))
    (fiberStageMorphism F J O n).modulePullback
    (modulePullback_additive (fiberStageMorphism F J O n)) inferInstance inferInstance

end CategoryTheory.Grothendieck

namespace CategoryTheory.Grothendieck

variable {F F' : SimplicialObject Cat.{v, u}}
variable (J : ∀ n, Precoverage (F.obj n)) (J' : ∀ n, Precoverage (F'.obj n))
variable [IsFiberwiseSite F J] [IsFiberwiseSite F' J']
variable [∀ n, HasSheafify (J n).toGrothendieck (Type w)]
variable [∀ n, HasSheafify (J' n).toGrothendieck (Type w)]
variable [HasSheafify (topology F J) (Type w)]
variable [HasSheafify (topology F' J') (Type w)]
variable [HasWeakSheafify (topology F J) (Type w)]
variable [HasWeakSheafify (topology F' J') (Type w)]
variable [∀ n, HasWeakSheafify (J n).toGrothendieck (Type w)]
variable [∀ n, HasWeakSheafify (J' n).toGrothendieck (Type w)]
variable (O : Sheaf (topology F J) RingCat.{w})
variable (O' : Sheaf (topology F' J') RingCat.{w})
variable [(topology F J).HasSheafCompose (CategoryTheory.forget RingCat.{w})]
variable [(topology F' J').HasSheafCompose (CategoryTheory.forget RingCat.{w})]
variable [∀ n, ((J n).toGrothendieck).HasSheafCompose (CategoryTheory.forget RingCat.{w})]
variable [∀ n, ((J' n).toGrothendieck).HasSheafCompose (CategoryTheory.forget RingCat.{w})]
variable [∀ n, ∀ P : (F.obj (op n))ᵒᵖ ⥤ Type w,
    (ι F (op n)).op.HasLeftKanExtension P]
variable [∀ n, ∀ P : (F'.obj (op n))ᵒᵖ ⥤ Type w,
    (ι F' (op n)).op.HasLeftKanExtension P]
variable [∀ n, ∀ P : (F.obj (op n))ᵒᵖ ⥤ Type w,
    (ι F (op n)).op.HasPointwiseRightKanExtension P]
variable [∀ n, ∀ P : (F'.obj (op n))ᵒᵖ ⥤ Type w,
    (ι F' (op n)).op.HasPointwiseRightKanExtension P]
variable [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (F.obj (op n))ᵒᵖ ⥤ Type w),
    ((F.map φ.op).toFunctor).op.HasPointwiseRightKanExtension P]
variable [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (F'.obj (op n))ᵒᵖ ⥤ Type w),
    ((F'.map φ.op).toFunctor).op.HasPointwiseRightKanExtension P]

namespace RingedMorphism

variable {J J' O O'}
variable (f : RingedMorphism J J' O O')
variable [∀ n (P : (F.obj n)ᵒᵖ ⥤ Type w),
    ((f.toSimplicial.app n).toFunctor).op.HasPointwiseRightKanExtension P]
variable [∀ P : (Grothendieck F)ᵒᵖ ⥤ Type w,
    (Grothendieck.map f.toSimplicial).op.HasPointwiseRightKanExtension P]
variable [∀ n, ∀ P : (F.obj (op n))ᵒᵖ ⥤ Type w,
    ((f.toSimplicial.app (op n)).toFunctor ⋙ ι F' (op n)).op.HasPointwiseRightKanExtension P]
variable [∀ n, ∀ P : (F.obj (op n))ᵒᵖ ⥤ Type w,
    (ι F (op n) ⋙ Grothendieck.map f.toSimplicial).op.HasPointwiseRightKanExtension P]
variable [∀ n, (SheafOfModules.restrictScalars.{w}
    (fiberStageMorphism F J O n).structureMap).IsRightAdjoint]
variable [∀ n, (SheafOfModules.restrictScalars.{w}
    (fiberStageMorphism F' J' O' n).structureMap).IsRightAdjoint]
variable [UnivLE.{max u v, w}]
variable [hTotal : HasModulePushforwardDerived (toToposHom f)]
variable [hComponent : ∀ n, HasModulePushforwardDerived (topos f n)]

/-- Cochain restriction of total module direct image is naturally isomorphic to
component direct image of cochain restriction. -/
def restrict_modulePushforward_cochain (n : SimplexCategory) :
    (@Functor.mapHomologicalComplex _ _ _ _ _ _ _ (toToposHom f).modulePushforward
      (@Functor.preservesZeroMorphisms_of_additive _ _ _ _ _ _ _
        (modulePushforward_additive (toToposHom f))) (up ℤ)) ⋙
        (fiberStageMorphism F' J' O' n).modulePullbackComplex ≅
      (fiberStageMorphism F J O n).modulePullbackComplex ⋙
        (@Functor.mapHomologicalComplex _ _ _ _ _ _ _ (topos f n).modulePushforward
      (@Functor.preservesZeroMorphisms_of_additive _ _ _ _ _ _ _
        (modulePushforward_additive (topos f n))) (up ℤ)) :=
  @NatIso.mapHomologicalComplex _ _ _ _ _ _ _ _ _
    (@Functor.preservesZeroMorphisms_comp _ _ _ _ _ _ _ _ _
      (toToposHom f).modulePushforward (fiberStageMorphism F' J' O' n).modulePullback
      (@Functor.preservesZeroMorphisms_of_additive _ _ _ _ _ _ _
          (modulePushforward_additive (toToposHom f)))
      (@Functor.preservesZeroMorphisms_of_additive _ _ _ _ _ _ _
          (modulePullback_additive (fiberStageMorphism F' J' O' n))))
    (@Functor.preservesZeroMorphisms_comp _ _ _ _ _ _ _ _ _
      (fiberStageMorphism F J O n).modulePullback (topos f n).modulePushforward
      (@Functor.preservesZeroMorphisms_of_additive _ _ _ _ _ _ _
          (modulePullback_additive (fiberStageMorphism F J O n)))
      (@Functor.preservesZeroMorphisms_of_additive _ _ _ _ _ _ _
          (modulePushforward_additive (topos f n))))
    (restrict_modulePushforward f n) (up ℤ)

/-- Restriction of derived total module direct image is a right derived functor
of the mixed cochain composite. -/
theorem restrict_modulePushforwardDerived_isRightDerived (n : SimplexCategory) :
    (modulePushforwardDerived (toToposHom f) ⋙ derivedModuleRestrict F' J' O' n).IsRightDerivedFunctor
      ((Functor.associator
            ((fiberStageMorphism F J O n).modulePullbackComplex)
            ((@Functor.mapHomologicalComplex _ _ _ _ _ _ _ (topos f n).modulePushforward
      (@Functor.preservesZeroMorphisms_of_additive _ _ _ _ _ _ _
        (modulePushforward_additive (topos f n))) (up ℤ)))
            ((@DerivedCategory.Q _ _ _ (Hom.moduleCat_hasDerivedCategory (fiberComponentRingedSite F' J' O' n))))).inv ≫
        Functor.whiskerRight (restrict_modulePushforward_cochain f n).inv
          ((@DerivedCategory.Q _ _ _ (Hom.moduleCat_hasDerivedCategory (fiberComponentRingedSite F' J' O' n)))) ≫
          (Functor.associator
                ((@Functor.mapHomologicalComplex _ _ _ _ _ _ _ (toToposHom f).modulePushforward
      (@Functor.preservesZeroMorphisms_of_additive _ _ _ _ _ _ _
        (modulePushforward_additive (toToposHom f))) (up ℤ)))
                ((fiberStageMorphism F' J' O' n).modulePullbackComplex)
                ((@DerivedCategory.Q _ _ _ (Hom.moduleCat_hasDerivedCategory (fiberComponentRingedSite F' J' O' n))))).hom ≫
            Functor.RightDerived.Composition.iteratedUnit
              ((@Functor.RightDerived.Homotopy.cochainUnit _ _ _ (Hom.moduleCat_hasDerivedCategory _)
      _ _ _ (Hom.moduleCat_hasDerivedCategory _) (toToposHom f).modulePushforward
      (modulePushforward_additive (toToposHom f)) hTotal))
              (derivedModuleRestrict_factors F' J' O' n).inv)
      (HomologicalComplex.quasiIso (SheafOfModules.{w} O) (up ℤ)) :=
  sorry

/-- The canonical comparison from restriction of derived total direct image to
derived component direct image of restriction. -/
def restrict_modulePushforwardDerived_hom (n : SimplexCategory) :
    modulePushforwardDerived (toToposHom f) ⋙ derivedModuleRestrict F' J' O' n ⟶
      derivedModuleRestrict F J O n ⋙ modulePushforwardDerived (topos f n) :=
  Functor.RightDerived.Composition.squareOfIso
    (hαGF := restrict_modulePushforwardDerived_isRightDerived f n)
    (HomologicalComplex.quasiIso (SheafOfModules.{w} O) (up ℤ))
    (restrict_modulePushforward_cochain f n)
    ((@Functor.RightDerived.Homotopy.cochainUnit _ _ _ (Hom.moduleCat_hasDerivedCategory _)
      _ _ _ (Hom.moduleCat_hasDerivedCategory _) (toToposHom f).modulePushforward
      (modulePushforward_additive (toToposHom f)) hTotal))
    (derivedModuleRestrict_factors F' J' O' n).inv
    (derivedModuleRestrict_factors F J O n).inv
    ((@Functor.RightDerived.Homotopy.cochainUnit _ _ _ (Hom.moduleCat_hasDerivedCategory _)
      _ _ _ (Hom.moduleCat_hasDerivedCategory _) (topos f n).modulePushforward
      (modulePushforward_additive (topos f n)) (hComponent n)))

/-- The canonical derived comparison factors the transported cochain unit through
restriction followed by component direct image. -/
theorem restrict_modulePushforwardDerived_hom_fac (n : SimplexCategory) :
    ((Functor.associator
            ((fiberStageMorphism F J O n).modulePullbackComplex)
            ((@Functor.mapHomologicalComplex _ _ _ _ _ _ _ (topos f n).modulePushforward
      (@Functor.preservesZeroMorphisms_of_additive _ _ _ _ _ _ _
        (modulePushforward_additive (topos f n))) (up ℤ)))
            ((@DerivedCategory.Q _ _ _ (Hom.moduleCat_hasDerivedCategory (fiberComponentRingedSite F' J' O' n))))).inv ≫
        Functor.whiskerRight (restrict_modulePushforward_cochain f n).inv
          ((@DerivedCategory.Q _ _ _ (Hom.moduleCat_hasDerivedCategory (fiberComponentRingedSite F' J' O' n)))) ≫
          (Functor.associator
                ((@Functor.mapHomologicalComplex _ _ _ _ _ _ _ (toToposHom f).modulePushforward
      (@Functor.preservesZeroMorphisms_of_additive _ _ _ _ _ _ _
        (modulePushforward_additive (toToposHom f))) (up ℤ)))
                ((fiberStageMorphism F' J' O' n).modulePullbackComplex)
                ((@DerivedCategory.Q _ _ _ (Hom.moduleCat_hasDerivedCategory (fiberComponentRingedSite F' J' O' n))))).hom ≫
            Functor.RightDerived.Composition.iteratedUnit
              ((@Functor.RightDerived.Homotopy.cochainUnit _ _ _ (Hom.moduleCat_hasDerivedCategory _)
      _ _ _ (Hom.moduleCat_hasDerivedCategory _) (toToposHom f).modulePushforward
      (modulePushforward_additive (toToposHom f)) hTotal))
              (derivedModuleRestrict_factors F' J' O' n).inv) ≫
      Functor.whiskerLeft ((@DerivedCategory.Q _ _ _ (Hom.moduleCat_hasDerivedCategory (fiberTotalRingedSite F J O))))
        (restrict_modulePushforwardDerived_hom f n) =
      Functor.RightDerived.Composition.iteratedUnit
        (derivedModuleRestrict_factors F J O n).inv
        ((@Functor.RightDerived.Homotopy.cochainUnit _ _ _ (Hom.moduleCat_hasDerivedCategory _)
      _ _ _ (Hom.moduleCat_hasDerivedCategory _) (topos f n).modulePushforward
      (modulePushforward_additive (topos f n)) (hComponent n))) :=
  sorry

/-- The derived mixed comparison is invertible. -/
instance restrict_modulePushforwardDerived_hom_isIso (n : SimplexCategory) :
    IsIso (restrict_modulePushforwardDerived_hom f n) :=
  sorry

/-- The canonical comparison between restriction of derived total direct image and
derived component direct image of restriction, evaluated at an unbounded derived module. -/
def restrict_modulePushforwardDerived_obj (n : SimplexCategory)
    (K : Hom.ModuleDerived.{w} (fiberTotalRingedSite F J O)) :
    (derivedModuleRestrict F' J' O' n).obj ((modulePushforwardDerived (toToposHom f)).obj K) ⟶
      (modulePushforwardDerived (topos f n)).obj ((derivedModuleRestrict F J O n).obj K) :=
  (restrict_modulePushforwardDerived_hom f n).app K

/-- The objectwise mixed comparison is invertible. -/
theorem restrict_modulePushforwardDerived_obj_isIso (n : SimplexCategory)
    (K : Hom.ModuleDerived.{w} (fiberTotalRingedSite F J O)) :
    IsIso (restrict_modulePushforwardDerived_obj f n K) :=
  sorry

end RingedMorphism

end CategoryTheory.Grothendieck
