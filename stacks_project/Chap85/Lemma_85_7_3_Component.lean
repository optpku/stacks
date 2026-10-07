module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.Module.Derived.Pullback
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.Module.Derived.Pushforward
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.Module.Pullback.Complex
public import ReasLib.CategoryTheory.DerivedCategory.Functor.TotalRightDerived
public import ReasLib.CategoryTheory.Functor.Derived.Composition.Right
public import stacks_project.Chap85.Lemma_85_7_2_Component

/-!
# Derived mixed identity for a morphism of ringed simplicial sites (case A)

A morphism of ringed simplicial sites in Situation 85.3.3 case A induces derived module
direct images `R h_total,*` and `R h_n,*`. Restriction along `g_n` commutes with unbounded
derived direct image: `(g'_n)^* ∘ R h_total,* ≅ R h_n,* ∘ g_n^*` on `D(O)`.
-/

@[expose] public section

universe u v w

open CategoryTheory CategoryTheory.Limits Opposite
open ComplexShape
open RingedSite
open RingedSite.ToposHom
open scoped MorphismOfTopoiIn

noncomputable section

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
variable [(SheafOfModules.restrictScalars.{w} (toToposHom f).structureMap).IsRightAdjoint]
variable [∀ n, (SheafOfModules.restrictScalars.{w} (topos f n).structureMap).IsRightAdjoint]
variable [HasModulePushforwardDerived (toToposHom f)]
variable [∀ n, HasModulePushforwardDerived (topos f n)]
variable [HasModulePullbackDerived (toToposHom f)]
variable [∀ n, HasModulePullbackDerived (topos f n)]
variable [∀ n, HasModulePullbackDerived (stageMorphism C J O n)]
variable [∀ n, HasModulePullbackDerived (stageMorphism C' J' O' n)]

-- Local instance justification (defeq pin): `moduleCat_hasDerivedCategory` is reducible to `HasDerivedCategory.standard` and is not global; `ModuleDerived`, homotopy total right derived module pushforward, and `mapDerivedCategory` of stage module pullback must share that same derived-category instance.
attribute [local instance] RingedSite.Hom.moduleCat_hasDerivedCategory

/-- Canonical derived-category structure on modules over the total site. -/
instance total_module_hasDerivedCategory :
    HasDerivedCategory (SheafOfModules.{w} O) :=
  Hom.moduleCat_hasDerivedCategory.{w, u, v, w} (totalRingedSite C J O)

/-- Canonical derived-category structure on modules over the target total site. -/
instance total'_module_hasDerivedCategory :
    HasDerivedCategory (SheafOfModules.{w} O') :=
  Hom.moduleCat_hasDerivedCategory.{w, u, v, w} (totalRingedSite C' J' O')

/-- Canonical derived-category structure on modules over the degree-`n` site. -/
instance component_module_hasDerivedCategory (n : SimplexCategory) :
    HasDerivedCategory (SheafOfModules.{w} (componentRingSheaf C J O n)) :=
  Hom.moduleCat_hasDerivedCategory.{w, u, v, w} (componentRingedSite C J O n)

/-- Canonical derived-category structure on modules over the target degree-`n` site. -/
instance component'_module_hasDerivedCategory (n : SimplexCategory) :
    HasDerivedCategory (SheafOfModules.{w} (componentRingSheaf C' J' O' n)) :=
  Hom.moduleCat_hasDerivedCategory.{w, u, v, w} (componentRingedSite C' J' O' n)

/-- Module pullback along `g_n` is additive. -/
instance stageMorphism_modulePullback_additive (n : SimplexCategory) :
    (stageMorphism C J O n).modulePullback.Additive :=
  modulePullback_additive (stageMorphism C J O n)

/-- Module pullback along `(g'_n)` is additive. -/
instance stageMorphism_modulePullback_additive' (n : SimplexCategory) :
    (stageMorphism C' J' O' n).modulePullback.Additive :=
  modulePullback_additive (stageMorphism C' J' O' n)

/-- Module direct image along `h_total` is additive. -/
instance toToposHom_modulePushforward_additive :
    (toToposHom f).modulePushforward.Additive :=
  modulePushforward_additive (toToposHom f)

/-- Module direct image along `h_n` is additive. -/
instance topos_modulePushforward_additive (n : SimplexCategory) :
    (topos f n).modulePushforward.Additive :=
  modulePushforward_additive (topos f n)

/-- Stage pullback `g_n^*` preserves finite limits, as `g_n^{-1} O = O_n`. -/
instance stageMorphism_modulePullback_preservesFiniteLimits (n : SimplexCategory) :
    PreservesFiniteLimits (stageMorphism C J O n).modulePullback :=
  sorry

/-- Stage pullback `(g'_n)^*` preserves finite limits, as `(g'_n)^{-1} O' = O'_n`. -/
instance stageMorphism_modulePullback_preservesFiniteLimits' (n : SimplexCategory) :
    PreservesFiniteLimits (stageMorphism C' J' O' n).modulePullback :=
  sorry

/-- Stage pullback `g_n^*` preserves finite colimits. -/
instance stageMorphism_modulePullback_preservesFiniteColimits (n : SimplexCategory) :
    PreservesFiniteColimits (stageMorphism C J O n).modulePullback :=
  sorry

/-- Stage pullback `(g'_n)^*` preserves finite colimits. -/
instance stageMorphism_modulePullback_preservesFiniteColimits' (n : SimplexCategory) :
    PreservesFiniteColimits (stageMorphism C' J' O' n).modulePullback :=
  sorry

/-- Homotopy-to-derived module pushforward along `h_total` admits a total right derived functor. -/
instance toToposHom_modulePushforward_hasRightDerived :
    (Functor.Homotopy.toDerived (toToposHom f).modulePushforward).HasRightDerivedFunctor
      (HomotopyCategory.quasiIso (SheafOfModules.{w} O) (up ℤ)) :=
  sorry

/-- Homotopy-to-derived module pushforward along `h_n` admits a total right derived functor. -/
instance topos_modulePushforward_hasRightDerived (n : SimplexCategory) :
    (Functor.Homotopy.toDerived (topos f n).modulePushforward).HasRightDerivedFunctor
      (HomotopyCategory.quasiIso (SheafOfModules.{w} (componentRingSheaf C J O n)) (up ℤ)) :=
  sorry

/-- Homotopy total right derived functor of `h_total,*` on modules. -/
abbrev derivedModulePushforwardTotal :
    Hom.ModuleDerived.{w} (totalRingedSite C J O) ⥤
      Hom.ModuleDerived.{w} (totalRingedSite C' J' O') :=
  Functor.RightDerived.Homotopy.functor (toToposHom f).modulePushforward

/-- Homotopy total right derived functor of `h_n,*` on modules. -/
abbrev derivedModulePushforward (n : SimplexCategory) :
    Hom.ModuleDerived.{w} (componentRingedSite C J O n) ⥤
      Hom.ModuleDerived.{w} (componentRingedSite C' J' O' n) :=
  Functor.RightDerived.Homotopy.functor (topos f n).modulePushforward

/-- Exact derived pullback `(g_n)^*` on `D(O)`. -/
abbrev derivedModulePullback (n : SimplexCategory) :
    Hom.ModuleDerived.{w} (totalRingedSite C J O) ⥤
      Hom.ModuleDerived.{w} (componentRingedSite C J O n) :=
  (stageMorphism C J O n).modulePullback.mapDerivedCategory

/-- Exact derived pullback `(g'_n)^*` on `D(O')`. -/
abbrev derivedModulePullback' (n : SimplexCategory) :
    Hom.ModuleDerived.{w} (totalRingedSite C' J' O') ⥤
      Hom.ModuleDerived.{w} (componentRingedSite C' J' O' n) :=
  (stageMorphism C' J' O' n).modulePullback.mapDerivedCategory

/-- Cochain-level form of the underived mixed identity
`(g'_n)^* ∘ h_total,* ≅ h_n,* ∘ g_n^*`. -/
def restrict_modulePushforward_cochain (n : SimplexCategory) :
    (toToposHom f).modulePushforward.mapHomologicalComplex (up ℤ) ⋙
        (stageMorphism C' J' O' n).modulePullback.mapHomologicalComplex (up ℤ) ≅
      (stageMorphism C J O n).modulePullback.mapHomologicalComplex (up ℤ) ⋙
        (topos f n).modulePushforward.mapHomologicalComplex (up ℤ) :=
  (Functor.mapHomologicalComplexCompIso
      (Iso.refl ((toToposHom f).modulePushforward ⋙
        (stageMorphism C' J' O' n).modulePullback)) (up ℤ)).symm ≪≫
    NatIso.mapHomologicalComplex (restrict_modulePushforward f n) (up ℤ) ≪≫
    Functor.mapHomologicalComplexCompIso
      (Iso.refl ((stageMorphism C J O n).modulePullback ⋙ (topos f n).modulePushforward))
      (up ℤ)

/-- Cochain-level unit of `R h_total,*` on modules. -/
def derivedModulePushforwardTotal_unit :
    (toToposHom f).modulePushforward.mapHomologicalComplex (up ℤ) ⋙
        (DerivedCategory.Q :
          CochainComplex (SheafOfModules.{w} O') ℤ ⥤
            Hom.ModuleDerived.{w} (totalRingedSite C' J' O')) ⟶
      (DerivedCategory.Q :
          CochainComplex (SheafOfModules.{w} O) ℤ ⥤
            Hom.ModuleDerived.{w} (totalRingedSite C J O)) ⋙
        derivedModulePushforwardTotal f :=
  Functor.RightDerived.Homotopy.cochainUnit (toToposHom f).modulePushforward

/-- Cochain-level unit of `R h_n,*` on modules. -/
def derivedModulePushforward_unit (n : SimplexCategory) :
    (topos f n).modulePushforward.mapHomologicalComplex (up ℤ) ⋙
        (DerivedCategory.Q :
          CochainComplex (SheafOfModules.{w} (componentRingSheaf C' J' O' n)) ℤ ⥤
            Hom.ModuleDerived.{w} (componentRingedSite C' J' O' n)) ⟶
      (DerivedCategory.Q :
          CochainComplex (SheafOfModules.{w} (componentRingSheaf C J O n)) ℤ ⥤
            Hom.ModuleDerived.{w} (componentRingedSite C J O n)) ⋙
        derivedModulePushforward f n :=
  Functor.RightDerived.Homotopy.cochainUnit (topos f n).modulePushforward

/-- Restriction after `R h_total,*` is a right-derived functor of the underived mixed
composite, using exactness of `(g'_n)^*`. -/
instance restrict_modulePushforwardDerived_isRightDerived (n : SimplexCategory) :
    (derivedModulePushforwardTotal f ⋙ derivedModulePullback' n).IsRightDerivedFunctor
      ((Functor.associator
            ((stageMorphism C J O n).modulePullback.mapHomologicalComplex (up ℤ))
            ((topos f n).modulePushforward.mapHomologicalComplex (up ℤ))
            DerivedCategory.Q).inv ≫
        Functor.whiskerRight (restrict_modulePushforward_cochain f n).inv
          DerivedCategory.Q ≫
          (Functor.associator
                ((toToposHom f).modulePushforward.mapHomologicalComplex (up ℤ))
                ((stageMorphism C' J' O' n).modulePullback.mapHomologicalComplex (up ℤ))
                DerivedCategory.Q).hom ≫
            Functor.RightDerived.Composition.iteratedUnit
              (derivedModulePushforwardTotal_unit f)
              (stageMorphism C' J' O' n).modulePullback.mapDerivedCategoryFactors.inv)
      (HomologicalComplex.quasiIso (SheafOfModules.{w} O) (up ℤ)) :=
  sorry

/-- Derived mixed comparison `(g'_n)^* ∘ R h_total,* ⟶ R h_n,* ∘ g_n^*`. -/
def restrict_modulePushforwardDerived_hom (n : SimplexCategory) :
    derivedModulePushforwardTotal f ⋙ derivedModulePullback' n ⟶
      derivedModulePullback n ⋙ derivedModulePushforward f n :=
  Functor.RightDerived.Composition.squareOfIso
    (HomologicalComplex.quasiIso (SheafOfModules.{w} O) (up ℤ))
    (restrict_modulePushforward_cochain f n)
    (derivedModulePushforwardTotal_unit f)
    (stageMorphism C' J' O' n).modulePullback.mapDerivedCategoryFactors.inv
    (stageMorphism C J O n).modulePullback.mapDerivedCategoryFactors.inv
    (derivedModulePushforward_unit f n)

/-- The derived mixed comparison is invertible. -/
theorem restrict_modulePushforwardDerived_hom_isIso (n : SimplexCategory) :
    IsIso (restrict_modulePushforwardDerived_hom f n) :=
  sorry

/-- Objectwise mixed comparison `(g'_n)^* (R h_total,* K) ⟶ R h_n,* (g_n^* K)`. -/
def restrict_modulePushforwardDerived_obj (n : SimplexCategory)
    (K : Hom.ModuleDerived.{w} (totalRingedSite C J O)) :
    (derivedModulePullback' n).obj ((derivedModulePushforwardTotal f).obj K) ⟶
      (derivedModulePushforward f n).obj ((derivedModulePullback n).obj K) :=
  (restrict_modulePushforwardDerived_hom f n).app K

/-- The objectwise mixed comparison is invertible. -/
theorem restrict_modulePushforwardDerived_obj_isIso (n : SimplexCategory)
    (K : Hom.ModuleDerived.{w} (totalRingedSite C J O)) :
    IsIso (restrict_modulePushforwardDerived_obj f n K) :=
  sorry


end RingedMorphism

end CategoryTheory.SimplicialSites
