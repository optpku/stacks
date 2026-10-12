/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.Module.Derived.Pullback
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.Module.Derived.Pushforward
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.Module.Pullback.Complex
public import ReasLib.CategoryTheory.DerivedCategory.Functor.TotalRightDerived
public import ReasLib.CategoryTheory.Functor.Derived.Composition.Right
public import stacks_project.Chap85.Lemma_85_7_2_Fiberwise

/-!
# Derived mixed identity for a fiberwise morphism of ringed simplicial sites (case B)

A morphism of ringed simplicial sites in Situation 85.3.3 case B induces derived module
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
    (IsFiberwiseMorphism.totalFunctor f.toSimplicial).op.HasPointwiseRightKanExtension P]
variable [∀ n, ∀ P : (F.obj (op n))ᵒᵖ ⥤ Type w,
    ((f.toSimplicial.app (op n)).toFunctor ⋙ ι F' (op n)).op.HasPointwiseRightKanExtension P]
variable [∀ n, ∀ P : (F.obj (op n))ᵒᵖ ⥤ Type w,
    (ι F (op n) ⋙ IsFiberwiseMorphism.totalFunctor f.toSimplicial).op.HasPointwiseRightKanExtension P]
variable [∀ n, (SheafOfModules.restrictScalars.{w}
    (fiberStageMorphism F J O n).structureMap).IsRightAdjoint]
variable [∀ n, (SheafOfModules.restrictScalars.{w}
    (fiberStageMorphism F' J' O' n).structureMap).IsRightAdjoint]
variable [UnivLE.{max u v, w}]
variable [(SheafOfModules.restrictScalars.{w} (toToposHom f).structureMap).IsRightAdjoint]
variable [∀ n, (SheafOfModules.restrictScalars.{w} (topos f n).structureMap).IsRightAdjoint]
variable [HasModulePushforwardDerived (toToposHom f)]
variable [∀ n, HasModulePushforwardDerived (topos f n)]
variable [HasModulePullbackDerived (toToposHom f)]
variable [∀ n, HasModulePullbackDerived (topos f n)]
variable [∀ n, HasModulePullbackDerived (fiberStageMorphism F J O n)]
variable [∀ n, HasModulePullbackDerived (fiberStageMorphism F' J' O' n)]

-- Local instance justification (defeq pin): `moduleCat_hasDerivedCategory` is reducible to `HasDerivedCategory.standard` and is not global; `ModuleDerived`, homotopy total right derived module pushforward, and `mapDerivedCategory` of fiber stage module pullback must share that same derived-category instance.
attribute [local instance] RingedSite.Hom.moduleCat_hasDerivedCategory

/-- Canonical derived-category structure on modules over the total site in case B. -/
instance fiberTotal_module_hasDerivedCategory :
    HasDerivedCategory (SheafOfModules.{w} O) :=
  Hom.moduleCat_hasDerivedCategory.{w, u, v, w} (fiberTotalRingedSite F J O)

/-- Canonical derived-category structure on modules over the target total site in case B. -/
instance fiberTotal'_module_hasDerivedCategory :
    HasDerivedCategory (SheafOfModules.{w} O') :=
  Hom.moduleCat_hasDerivedCategory.{w, u, v, w} (fiberTotalRingedSite F' J' O')

/-- Canonical derived-category structure on modules over the degree-`n` fiber site. -/
instance fiberComponent_module_hasDerivedCategory (n : SimplexCategory) :
    HasDerivedCategory (SheafOfModules.{w} (fiberComponentRingSheaf F J O n)) :=
  Hom.moduleCat_hasDerivedCategory.{w, u, v, w} (fiberComponentRingedSite F J O n)

/-- Canonical derived-category structure on modules over the target degree-`n` fiber site. -/
instance fiberComponent'_module_hasDerivedCategory (n : SimplexCategory) :
    HasDerivedCategory (SheafOfModules.{w} (fiberComponentRingSheaf F' J' O' n)) :=
  Hom.moduleCat_hasDerivedCategory.{w, u, v, w} (fiberComponentRingedSite F' J' O' n)

/-- Module pullback along `g_n` is additive in case B. -/
instance fiberStageMorphism_modulePullback_additive (n : SimplexCategory) :
    (fiberStageMorphism F J O n).modulePullback.Additive :=
  modulePullback_additive (fiberStageMorphism F J O n)

/-- Module pullback along `(g'_n)` is additive in case B. -/
instance fiberStageMorphism_modulePullback_additive' (n : SimplexCategory) :
    (fiberStageMorphism F' J' O' n).modulePullback.Additive :=
  modulePullback_additive (fiberStageMorphism F' J' O' n)

/-- Module direct image along `h_total` is additive in case B. -/
instance toToposHom_modulePushforward_additive :
    (toToposHom f).modulePushforward.Additive :=
  modulePushforward_additive (toToposHom f)

/-- Module direct image along `h_n` is additive in case B. -/
instance topos_modulePushforward_additive (n : SimplexCategory) :
    (topos f n).modulePushforward.Additive :=
  modulePushforward_additive (topos f n)

/-- Fiber stage pullback `g_n^*` preserves finite limits, as `g_n^{-1} O = O_n`. -/
instance fiberStageMorphism_modulePullback_preservesFiniteLimits (n : SimplexCategory) :
    PreservesFiniteLimits (fiberStageMorphism F J O n).modulePullback :=
  sorry

/-- Fiber stage pullback `(g'_n)^*` preserves finite limits, as `(g'_n)^{-1} O' = O'_n`. -/
instance fiberStageMorphism_modulePullback_preservesFiniteLimits' (n : SimplexCategory) :
    PreservesFiniteLimits (fiberStageMorphism F' J' O' n).modulePullback :=
  sorry

/-- Fiber stage pullback `g_n^*` preserves finite colimits. -/
instance fiberStageMorphism_modulePullback_preservesFiniteColimits (n : SimplexCategory) :
    PreservesFiniteColimits (fiberStageMorphism F J O n).modulePullback :=
  sorry

/-- Fiber stage pullback `(g'_n)^*` preserves finite colimits. -/
instance fiberStageMorphism_modulePullback_preservesFiniteColimits' (n : SimplexCategory) :
    PreservesFiniteColimits (fiberStageMorphism F' J' O' n).modulePullback :=
  sorry

/-- Homotopy-to-derived module pushforward along `h_total` admits a total right derived functor. -/
instance toToposHom_modulePushforward_hasRightDerived :
    (Functor.Homotopy.toDerived (toToposHom f).modulePushforward).HasRightDerivedFunctor
      (HomotopyCategory.quasiIso (SheafOfModules.{w} O) (up ℤ)) :=
  sorry

/-- Homotopy-to-derived module pushforward along `h_n` admits a total right derived functor. -/
instance topos_modulePushforward_hasRightDerived (n : SimplexCategory) :
    (Functor.Homotopy.toDerived (topos f n).modulePushforward).HasRightDerivedFunctor
      (HomotopyCategory.quasiIso (SheafOfModules.{w} (fiberComponentRingSheaf F J O n))
        (up ℤ)) :=
  sorry

/-- Homotopy total right derived functor of `h_total,*` on modules in case B. -/
abbrev derivedModulePushforwardTotal :
    Hom.ModuleDerived.{w} (fiberTotalRingedSite F J O) ⥤
      Hom.ModuleDerived.{w} (fiberTotalRingedSite F' J' O') :=
  Functor.RightDerived.Homotopy.functor (toToposHom f).modulePushforward

/-- Homotopy total right derived functor of `h_n,*` on modules in case B. -/
abbrev derivedModulePushforward (n : SimplexCategory) :
    Hom.ModuleDerived.{w} (fiberComponentRingedSite F J O n) ⥤
      Hom.ModuleDerived.{w} (fiberComponentRingedSite F' J' O' n) :=
  Functor.RightDerived.Homotopy.functor (topos f n).modulePushforward

/-- Exact derived pullback `(g_n)^*` on `D(O)` in case B. -/
abbrev derivedModulePullback (n : SimplexCategory) :
    Hom.ModuleDerived.{w} (fiberTotalRingedSite F J O) ⥤
      Hom.ModuleDerived.{w} (fiberComponentRingedSite F J O n) :=
  (fiberStageMorphism F J O n).modulePullback.mapDerivedCategory

/-- Exact derived pullback `(g'_n)^*` on `D(O')` in case B. -/
abbrev derivedModulePullback' (n : SimplexCategory) :
    Hom.ModuleDerived.{w} (fiberTotalRingedSite F' J' O') ⥤
      Hom.ModuleDerived.{w} (fiberComponentRingedSite F' J' O' n) :=
  (fiberStageMorphism F' J' O' n).modulePullback.mapDerivedCategory

/-- Cochain-level form of the underived mixed identity
`(g'_n)^* ∘ h_total,* ≅ h_n,* ∘ g_n^*` in case B. -/
def restrict_modulePushforward_cochain (n : SimplexCategory) :
    (toToposHom f).modulePushforward.mapHomologicalComplex (up ℤ) ⋙
        (fiberStageMorphism F' J' O' n).modulePullback.mapHomologicalComplex (up ℤ) ≅
      (fiberStageMorphism F J O n).modulePullback.mapHomologicalComplex (up ℤ) ⋙
        (topos f n).modulePushforward.mapHomologicalComplex (up ℤ) :=
  (Functor.mapHomologicalComplexCompIso
      (Iso.refl ((toToposHom f).modulePushforward ⋙
        (fiberStageMorphism F' J' O' n).modulePullback)) (up ℤ)).symm ≪≫
    NatIso.mapHomologicalComplex (restrict_modulePushforward f n) (up ℤ) ≪≫
    Functor.mapHomologicalComplexCompIso
      (Iso.refl ((fiberStageMorphism F J O n).modulePullback ⋙
        (topos f n).modulePushforward))
      (up ℤ)

/-- Cochain-level unit of `R h_total,*` on modules in case B. -/
def derivedModulePushforwardTotal_unit :
    (toToposHom f).modulePushforward.mapHomologicalComplex (up ℤ) ⋙
        (DerivedCategory.Q :
          CochainComplex (SheafOfModules.{w} O') ℤ ⥤
            Hom.ModuleDerived.{w} (fiberTotalRingedSite F' J' O')) ⟶
      (DerivedCategory.Q :
          CochainComplex (SheafOfModules.{w} O) ℤ ⥤
            Hom.ModuleDerived.{w} (fiberTotalRingedSite F J O)) ⋙
        derivedModulePushforwardTotal f :=
  Functor.RightDerived.Homotopy.cochainUnit (toToposHom f).modulePushforward

/-- Cochain-level unit of `R h_n,*` on modules in case B. -/
def derivedModulePushforward_unit (n : SimplexCategory) :
    (topos f n).modulePushforward.mapHomologicalComplex (up ℤ) ⋙
        (DerivedCategory.Q :
          CochainComplex (SheafOfModules.{w} (fiberComponentRingSheaf F' J' O' n)) ℤ ⥤
            Hom.ModuleDerived.{w} (fiberComponentRingedSite F' J' O' n)) ⟶
      (DerivedCategory.Q :
          CochainComplex (SheafOfModules.{w} (fiberComponentRingSheaf F J O n)) ℤ ⥤
            Hom.ModuleDerived.{w} (fiberComponentRingedSite F J O n)) ⋙
        derivedModulePushforward f n :=
  Functor.RightDerived.Homotopy.cochainUnit (topos f n).modulePushforward

/-- Restriction after `R h_total,*` is a right-derived functor of the underived mixed
composite in case B, using exactness of `(g'_n)^*`. -/
instance restrict_modulePushforwardDerived_isRightDerived (n : SimplexCategory) :
    (derivedModulePushforwardTotal f ⋙ derivedModulePullback' n).IsRightDerivedFunctor
      ((Functor.associator
            ((fiberStageMorphism F J O n).modulePullback.mapHomologicalComplex (up ℤ))
            ((topos f n).modulePushforward.mapHomologicalComplex (up ℤ))
            DerivedCategory.Q).inv ≫
        Functor.whiskerRight (restrict_modulePushforward_cochain f n).inv
          DerivedCategory.Q ≫
          (Functor.associator
                ((toToposHom f).modulePushforward.mapHomologicalComplex (up ℤ))
                ((fiberStageMorphism F' J' O' n).modulePullback.mapHomologicalComplex (up ℤ))
                DerivedCategory.Q).hom ≫
            Functor.RightDerived.Composition.iteratedUnit
              (derivedModulePushforwardTotal_unit f)
              (fiberStageMorphism F' J' O' n).modulePullback.mapDerivedCategoryFactors.inv)
      (HomologicalComplex.quasiIso (SheafOfModules.{w} O) (up ℤ)) :=
  sorry

/-- Derived mixed comparison `(g'_n)^* ∘ R h_total,* ⟶ R h_n,* ∘ g_n^*` in case B. -/
def restrict_modulePushforwardDerived_hom (n : SimplexCategory) :
    derivedModulePushforwardTotal f ⋙ derivedModulePullback' n ⟶
      derivedModulePullback n ⋙ derivedModulePushforward f n :=
  Functor.RightDerived.Composition.squareOfIso
    (HomologicalComplex.quasiIso (SheafOfModules.{w} O) (up ℤ))
    (restrict_modulePushforward_cochain f n)
    (derivedModulePushforwardTotal_unit f)
    (fiberStageMorphism F' J' O' n).modulePullback.mapDerivedCategoryFactors.inv
    (fiberStageMorphism F J O n).modulePullback.mapDerivedCategoryFactors.inv
    (derivedModulePushforward_unit f n)

/-- The derived mixed comparison is invertible in case B. -/
theorem restrict_modulePushforwardDerived_hom_isIso (n : SimplexCategory) :
    IsIso (restrict_modulePushforwardDerived_hom f n) :=
  sorry

/-- Objectwise mixed comparison `(g'_n)^* (R h_total,* K) ⟶ R h_n,* (g_n^* K)` in case B. -/
def restrict_modulePushforwardDerived_obj (n : SimplexCategory)
    (K : Hom.ModuleDerived.{w} (fiberTotalRingedSite F J O)) :
    (derivedModulePullback' n).obj ((derivedModulePushforwardTotal f).obj K) ⟶
      (derivedModulePushforward f n).obj ((derivedModulePullback n).obj K) :=
  (restrict_modulePushforwardDerived_hom f n).app K

/-- The objectwise mixed comparison is invertible in case B. -/
theorem restrict_modulePushforwardDerived_obj_isIso (n : SimplexCategory)
    (K : Hom.ModuleDerived.{w} (fiberTotalRingedSite F J O)) :
    IsIso (restrict_modulePushforwardDerived_obj f n K) :=
  sorry


end RingedMorphism

end CategoryTheory.Grothendieck
