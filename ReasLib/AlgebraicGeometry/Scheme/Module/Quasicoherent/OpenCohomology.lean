module

public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Sections.Underlying.Cohomology
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent
public import ReasLib.AlgebraicGeometry.Scheme.Module.Quasicoherent.Grothendieck
public import ReasLib.AlgebraicGeometry.Scheme.Module.RingedSpace
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.RightDerived.Degree.InjectiveResolution
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Composition.BoundedBelow.Square.Exact
public import ReasLib.CategoryTheory.Sites.Cohomology.SectionsComparison
public import ReasLib.Topology.Sheaf.Derived.Basic

/-!
# Cohomology on open subsets for quasicoherent modules

This module compares right-derived sections in the category of quasicoherent modules with
cohomology of the underlying additive sheaf on an open subset.
-/

@[expose] public section

open CategoryTheory Limits TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.QCoh

/-- The abelian-group-valued sections functor on an open subset, restricted to quasicoherent
modules. -/
abbrev openSectionsFunctor (X : Scheme.{u}) (U : TopologicalSpace.Opens X.carrier) :
    QCoh X ⥤ AddCommGrpCat.{u} :=
  inclusion X ⋙ Scheme.Modules.toRingedSpace X ⋙
    RingedSpace.moduleSectionsAsAbelianFunctor X.toRingedSpace U

/-- The quasicoherent open-sections functor is additive. -/
instance openSectionsFunctor_additive
    (X : Scheme.{u}) (U : TopologicalSpace.Opens X.carrier) :
    (openSectionsFunctor X U).Additive := sorry

/-- Cohomology on an open subset of the underlying additive sheaf, restricted to quasicoherent
modules. -/
abbrev openCohomologyFunctor
    (X : Scheme.{u}) (U : TopologicalSpace.Opens X.carrier) (i : ℕ) :
    QCoh X ⥤ AddCommGrpCat.{u} :=
  inclusion X ⋙ Scheme.Modules.toRingedSpace X ⋙
    RingedSpace.Module.Derived.Sections.Underlying.cohomologyFunctor
      (X := X.toRingedSpace) U i

/-- Evaluation of `openCohomologyFunctor` is the cohomology of the underlying additive sheaf of
the corresponding ringed-space module. -/
theorem openCohomologyFunctor_obj
    (X : Scheme.{u}) (U : TopologicalSpace.Opens X.carrier) (i : ℕ) (F : QCoh X) :
    (openCohomologyFunctor X U i).obj F =
      ((RingedSpace.moduleUnderlyingSheaf X.toRingedSpace).obj
        ((Scheme.Modules.toRingedSpace X).obj ((inclusion X).obj F))).H' i U := sorry

/-- The canonical comparison from right-derived quasicoherent sections on an open subset to
cohomology of the underlying additive sheaf. -/
noncomputable def openDerivedSectionsComparison
    (X : Scheme.{u}) (U : TopologicalSpace.Opens X.carrier) (i : ℕ) :
    (openSectionsFunctor X U).rightDerived i ⟶ openCohomologyFunctor X U i := by
  let I₁ : QCoh X ⥤ₑ X.Modules := ExactFunctor.of (inclusion X)
  let I₂ : X.Modules ⥤ₑ X.toRingedSpace.Modules :=
    ExactFunctor.of (Scheme.Modules.ringedSpaceEquivalence X).functor
  let I₃ : X.toRingedSpace.Modules ⥤ₑ
      X.carrier.Sheaf AddCommGrpCat.{u} :=
    ⟨RingedSpace.moduleUnderlyingSheaf X.toRingedSpace,
      (exactFunctor_iff _).2
        ⟨RingedSpace.moduleUnderlyingSheaf_preservesFiniteLimits X.toRingedSpace,
          RingedSpace.moduleUnderlyingSheaf_preservesFiniteColimits X.toRingedSpace⟩⟩
  let I := (I₁.comp I₂).comp I₃
  let H : X.carrier.Sheaf AddCommGrpCat.{u} ⥤ AddCommGrpCat.{u} :=
    siteAbelianSectionsFunctor (Opens.grothendieckTopology X.carrier) U
  let hI : I.obj.Additive := ExactFunctor.additive I
  let hH : H.Additive := by
    dsimp [H]
    exact siteAbelianSectionsFunctor_additive
      (Opens.grothendieckTopology X.carrier) U
  let hIH : (I.obj ⋙ H).Additive :=
    { map_add := by
        intro X Y f g
        change H.map (I.obj.map (f + g)) = _
        rw [hI.map_add, hH.map_add]
        rfl }
  let hEnoughQCoh : EnoughInjectives (QCoh X) :=
    @IsGrothendieckAbelian.enoughInjectives.{u, u, u + 1}
      (QCoh X) inferInstance inferInstance (instIsGrothendieckAbelian.{u, u} X)
  let hRF : (openSectionsFunctor X U).toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso (QCoh X)) :=
    @Functor.RightDerived.Bounded.hasDerived _ _ _ _ _ _ _
      (openSectionsFunctor X U) (openSectionsFunctor_additive X U)
      (@Functor.RightAcyclic.Bounded.hasMonoEmbedding _ _ _ _ _ _ _
        (openSectionsFunctor X U) (openSectionsFunctor_additive X U) hEnoughQCoh)
  let hRH : H.toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso (X.carrier.Sheaf AddCommGrpCat.{u})) :=
    @Functor.RightDerived.Bounded.hasDerived _ _ _ _ _ _ _ H hH inferInstance
  let hRIH : (I.obj ⋙ H).toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso (QCoh X)) :=
    @Functor.RightDerived.Bounded.hasDerived _ _ _ _ _ _ _ (I.obj ⋙ H) hIH
      (@Functor.RightAcyclic.Bounded.hasMonoEmbedding _ _ _ _ _ _ _
        (I.obj ⋙ H) hIH hEnoughQCoh)
  let hRI : I.obj.toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso (QCoh X)) :=
    @Functor.RightDerived.Bounded.hasDerived _ _ _ _ _ _ _ I.obj hI
      (@Functor.RightAcyclic.Bounded.hasMonoEmbedding _ _ _ _ _ _ _ I.obj hI hEnoughQCoh)
  let RF := @Functor.RightDerived.Bounded.functor _ _ _ _ _ _ _ _
    (openSectionsFunctor X U) (openSectionsFunctor_additive X U) hRF
  let RH := @Functor.RightDerived.Bounded.functor _ _ _ _ _ _ _ _ H hH hRH
  let τ : openSectionsFunctor X U ⟶ I.obj ⋙ H :=
    (Functor.isoWhiskerLeft I.obj
      (sheafSectionsNatIsoEvaluation
        (J := Opens.grothendieckTopology X.carrier)
        (A := AddCommGrpCat.{u}) (X := U))).inv
  let η : RF ⟶ ExactFunctor.Derived.Plus.functor I ⋙ RH :=
    @Functor.RightDerived.Bounded.map _ _ _ _ _ _ _ _
        (openSectionsFunctor X U) (I.obj ⋙ H)
        (openSectionsFunctor_additive X U) hIH hRF hRIH τ ≫
      @Functor.RightDerived.Composition.BoundedBelow.Square.Exact.targetComparison
        _ _ _ _ _ _ _ _ _ _ _ _ I H hH hRH hRIH hRI
  let eSingleComp :
      (DerivedCategory.Plus.singleFunctor (QCoh X) 0 ⋙
          ExactFunctor.Derived.Plus.functor I) ⋙ DerivedCategory.Plus.ι ≅
        (I.obj ⋙ DerivedCategory.Plus.singleFunctor
          (X.carrier.Sheaf AddCommGrpCat.{u}) 0) ⋙ DerivedCategory.Plus.ι :=
    Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (ExactFunctor.Derived.Plus.compιIso I) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight
        (DerivedCategory.Plus.singleFunctorιIso (QCoh X) 0) I.obj.mapDerivedCategory ≪≫
      I.obj.mapDerivedCategorySingleFunctor 0 ≪≫
      Functor.isoWhiskerLeft I.obj
        (DerivedCategory.Plus.singleFunctorιIso
          (X.carrier.Sheaf AddCommGrpCat.{u}) 0).symm ≪≫
      (Functor.associator _ _ _).symm
  let eSingle := Functor.fullyFaithfulCancelRight DerivedCategory.Plus.ι eSingleComp
  let eTarget :
      Functor.RightDerived.degree
          (ExactFunctor.Derived.Plus.functor I ⋙ RH) (i : ℤ) ≅
        I.obj ⋙ Functor.RightDerived.degree RH (i : ℤ) :=
    Functor.isoWhiskerLeft (DerivedCategory.Plus.singleFunctor (QCoh X) 0)
        (Functor.associator (ExactFunctor.Derived.Plus.functor I)
          RH
          (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u} (i : ℤ))) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight eSingle
        (RH ⋙
          DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u} (i : ℤ)) ≪≫
      Functor.associator _ _ _
  exact
    (Functor.RightDerived.Bounded.degree.degreeFunctorIsoRightDerived
      (openSectionsFunctor X U) i).inv ≫
      Functor.RightDerived.degree.map η (i : ℤ) ≫
      eTarget.hom ≫
      Functor.whiskerLeft I.obj
        (@Functor.RightDerived.Bounded.degree.degreeFunctorIsoRightDerived
          _ _ _ _ _ _ _ _ _ H hH hRH i).hom ≫
      Functor.whiskerLeft I.obj
        (SiteAbelianSectionsDerived.HPrime.rightDerivedSectionsIso
          (Opens.grothendieckTopology X.carrier) U i).inv

/-- A comparison from degree-one derived quasicoherent sections to underlying-sheaf cohomology
is not invertible at an object where its source vanishes and its target does not. -/
theorem openComparisonComponent_not_isIso
    (X : Scheme.{u}) (U : TopologicalSpace.Opens X.carrier) (M : QCoh X)
    (hR : IsZero (((openSectionsFunctor X U).rightDerived 1).obj M))
    (hH : ¬ IsZero ((openCohomologyFunctor X U 1).obj M))
    (t : (openSectionsFunctor X U).rightDerived 1 ⟶ openCohomologyFunctor X U 1) :
    ¬ IsIso (t.app M) := sorry

/-- There are a commutative ring `A`, an injective `A`-module `I`, and a quasi-compact open
subset `U` of `Spec A` such that degree-one derived quasicoherent sections of `Ĩ` on `U`
vanish while degree-one cohomology of its underlying additive sheaf does not vanish. -/
theorem existsAffineDerivedSectionsCounterexample :
    ∃ (A : CommRingCat.{u}) (I : ModuleCat A) (U : CompactOpens (Spec A).carrier),
      Injective I ∧
        IsZero
          (((openSectionsFunctor (Spec A) U.toOpens).rightDerived 1).obj
            ((AlgebraicGeometry.tildeEquiv : ModuleCat A ≌ QCoh (Spec A)).functor.obj I)) ∧
        ¬ IsZero
          ((openCohomologyFunctor (Spec A) U.toOpens 1).obj
            ((AlgebraicGeometry.tildeEquiv : ModuleCat A ≌ QCoh (Spec A)).functor.obj I)) := sorry

/-- On some affine scheme, the canonical degree-one comparison from derived quasicoherent
sections to cohomology of the underlying additive sheaf is not invertible at an injective
module, even though its source vanishes. -/
theorem existsAffineOpenDerivedSectionsComparison_not_isIso :
    ∃ (A : CommRingCat.{u}) (I : ModuleCat A) (U : CompactOpens (Spec A).carrier),
      Injective I ∧
        IsZero
          (((openSectionsFunctor (Spec A) U.toOpens).rightDerived 1).obj
            ((AlgebraicGeometry.tildeEquiv : ModuleCat A ≌ QCoh (Spec A)).functor.obj I)) ∧
        ¬ IsZero
          ((openCohomologyFunctor (Spec A) U.toOpens 1).obj
            ((AlgebraicGeometry.tildeEquiv : ModuleCat A ≌ QCoh (Spec A)).functor.obj I)) ∧
        ¬ IsIso
          ((openDerivedSectionsComparison (Spec A) U.toOpens 1).app
            ((AlgebraicGeometry.tildeEquiv : ModuleCat A ≌ QCoh (Spec A)).functor.obj I)) := sorry

end AlgebraicGeometry.Scheme.QCoh
