module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.HigherDirectImage
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.ClosedImmersion
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Pullback
public import ReasLib.CategoryTheory.Abelian.Injective.RightDerived.Composition
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Composition.BoundedBelow
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Exact.Bounded.RightDerived
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.RightDerived.Degree.InjectiveResolution

/-! Higher direct images across a closed immersion. -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.AlgebraicSpace

noncomputable section
universe u

-- Local instance justification (defeq pin): `HasInjectiveResolutions` and `higherDirectImage` pin the Abelian-induced `Preadditive`/`HasZeroMorphisms` instances for defeq of `cohomologyOver`.
attribute [local instance 2000] Abelian.toPreadditive Preadditive.preadditiveHasZeroMorphisms

namespace AlgebraicGeometry.AlgebraicSpace.Modules

variable {S : Scheme.{u}} {Z X Y : AlgebraicSpace S}
variable (i : Z ⟶ X) [IsClosedImmersion i] (f : X ⟶ Y)
variable [Abelian Z.Modules] [Abelian X.Modules] [Abelian Y.Modules]
variable [HasInjectiveResolutions Z.Modules] [HasInjectiveResolutions X.Modules]

/-- Module pushforward along a closed immersion, bundled with its exactness. -/
private def closedImmersionPushforward : Z.Modules ⥤ₑ X.Modules :=
  ⟨pushforward i, pushforward_exact i⟩

/-- Injective resolutions supply monomorphisms into their degree-zero injectives. -/
private theorem enoughInjectivesOfResolutions (A : Type*) [Category A] [Abelian A]
    [HasInjectiveResolutions A] : EnoughInjectives A where
  presentation M := ⟨{
    J := (injectiveResolution M).cocomplex.X 0
    f := (injectiveResolution M).ι.f 0
    mono := Limits.mono_of_isLimit_fork (injectiveResolution M).isLimitKernelFork }⟩

section DerivedModels

variable [sourceDerived : HasDerivedCategory.{u + 1} Z.Modules]
variable [middleDerived : HasDerivedCategory.{u + 1} X.Modules]
variable [targetDerived : HasDerivedCategory.{u + 1} Y.Modules]
variable [sourceEnough : EnoughInjectives Z.Modules] [middleEnough : EnoughInjectives X.Modules]

/-- Exact pushforward takes a degree-zero derived object to the degree-zero
object of its module pushforward. -/
private def closedImmersionExactSingleIso :
    DerivedCategory.Plus.singleFunctor Z.Modules 0 ⋙
        ExactFunctor.Derived.Plus.functor (closedImmersionPushforward i) ≅
      (pushforward i) ⋙ DerivedCategory.Plus.singleFunctor X.Modules 0 :=
  Functor.fullyFaithfulCancelRight DerivedCategory.Plus.ι
    (Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft (DerivedCategory.Plus.singleFunctor Z.Modules 0)
        (ExactFunctor.Derived.Plus.compιIso (closedImmersionPushforward i)) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (DerivedCategory.Plus.singleFunctorιIso Z.Modules 0)
        (closedImmersionPushforward i).obj.mapDerivedCategory ≪≫
      (closedImmersionPushforward i).obj.mapDerivedCategorySingleFunctor 0 ≪≫
      (Functor.isoWhiskerLeft (pushforward i)
        (DerivedCategory.Plus.singleFunctorιIso X.Modules 0)).symm)

/-- Degreewise Leray comparison formed from the derived-composition map
and the exact action of closed-immersion pushforward on single objects. -/
private def closedImmersionLerayComparisonCore (M : Z.Modules) (p : ℕ) :
    higherDirectImage (i ≫ f) M p ⟶
      higherDirectImage f ((pushforward i).obj M) p :=
  (Functor.RightDerived.Bounded.degree.degreeIsoRightDerived
      (pushforward (i ≫ f)) p M).inv ≫
    (DerivedCategory.Plus.homologyFunctor Y.Modules (Int.ofNat p)).map
      ((Functor.RightDerived.Composition.BoundedBelow.comparisonOfIso
          (pushforward i) (pushforward f) (pushforwardComp i f).symm).app
          ((DerivedCategory.Plus.singleFunctor Z.Modules 0).obj M) ≫
        (Functor.RightDerived.Bounded.functor (pushforward f)).map
          (((ExactFunctor.Derived.Plus.rightDerivedIso
              (closedImmersionPushforward i)).app
                ((DerivedCategory.Plus.singleFunctor Z.Modules 0).obj M)).hom ≫
            (closedImmersionExactSingleIso i).hom.app M)) ≫
    (Functor.RightDerived.Bounded.degree.degreeIsoRightDerived
      (pushforward f) p ((pushforward i).obj M)).hom

end DerivedModels

/-- The canonical Leray comparison from the higher direct image of a composite
with a closed immersion to the higher direct image of its exact pushforward. -/
@[no_expose]
def closedImmersionLerayComparison (M : Z.Modules) (p : ℕ) :
    higherDirectImage (i ≫ f) M p ⟶
      higherDirectImage f ((pushforward i).obj M) p :=
  closedImmersionLerayComparisonCore i f M p
    (sourceDerived := HasDerivedCategory.standard Z.Modules)
    (middleDerived := HasDerivedCategory.standard X.Modules)
    (targetDerived := HasDerivedCategory.standard Y.Modules)
    (sourceEnough := enoughInjectivesOfResolutions Z.Modules)
    (middleEnough := enoughInjectivesOfResolutions X.Modules)

/-- A preimage under the Leray comparison on sections, with zero fallback. -/
private def closedImmersionLerayInverseSection (M : Z.Modules) (p : ℕ)
    (U : (smallEtaleSite Y)ᵒᵖ) :
    (higherDirectImage f ((pushforward i).obj M) p).val.obj U →
      (higherDirectImage (i ≫ f) M p).val.obj U :=
  fun y ↦ @dite _
    (∃ x, ((closedImmersionLerayComparison i f M p).val.app U).hom x = y)
    (Classical.propDecidable _) (fun h ↦ h.choose) (fun _ ↦ 0)

/-- The selected inverse section functions preserve addition. -/
private theorem closedImmersionLerayInverse_map_add (M : Z.Modules) (p : ℕ)
    (U : (smallEtaleSite Y)ᵒᵖ)
    (x y : (higherDirectImage f ((pushforward i).obj M) p).val.obj U) :
    closedImmersionLerayInverseSection i f M p U (x + y) =
      closedImmersionLerayInverseSection i f M p U x +
        closedImmersionLerayInverseSection i f M p U y := sorry

/-- The selected inverse section functions preserve the structure-sheaf action. -/
private theorem closedImmersionLerayInverse_map_smul (M : Z.Modules) (p : ℕ)
    (U : (smallEtaleSite Y)ᵒᵖ) (r : (structureSheaf Y).obj.obj U)
    (x : (higherDirectImage f ((pushforward i).obj M) p).val.obj U) :
    closedImmersionLerayInverseSection i f M p U (r • x) =
      r • closedImmersionLerayInverseSection i f M p U x := sorry

/-- The sectionwise inverse comparison as a structure-sheaf-linear section map. -/
private def closedImmersionLerayInverseSectionHom (M : Z.Modules) (p : ℕ)
    (U : (smallEtaleSite Y)ᵒᵖ) :
    (higherDirectImage f ((pushforward i).obj M) p).val.obj U ⟶
      (higherDirectImage (i ≫ f) M p).val.obj U :=
  let A := (higherDirectImage f ((pushforward i).obj M) p).val.obj U
  let B := (higherDirectImage (i ≫ f) M p).val.obj U
  @ModuleCat.ofHom ((structureSheaf Y).obj.obj U) _ A B
    A.isAddCommGroup A.isModule B.isAddCommGroup B.isModule
    { toFun := closedImmersionLerayInverseSection i f M p U
      map_add' := closedImmersionLerayInverse_map_add i f M p U
      map_smul' := closedImmersionLerayInverse_map_smul i f M p U }

/-- The inverse section maps commute with restriction. -/
private theorem closedImmersionLerayInverse_naturality (M : Z.Modules) (p : ℕ)
    {U V : (smallEtaleSite Y)ᵒᵖ} (g : U ⟶ V) :
    (higherDirectImage f ((pushforward i).obj M) p).val.map g ≫
        (ModuleCat.restrictScalars ((structureSheaf Y).obj.map g).hom).map
          (closedImmersionLerayInverseSectionHom i f M p V) =
      closedImmersionLerayInverseSectionHom i f M p U ≫
        (higherDirectImage (i ≫ f) M p).val.map g := sorry

/-- The inverse Leray morphism, assembled from the selected section preimages. -/
@[no_expose]
def closedImmersionLerayInverse (M : Z.Modules) (p : ℕ) :
    higherDirectImage f ((pushforward i).obj M) p ⟶
      higherDirectImage (i ≫ f) M p where
  val :=
    { app := closedImmersionLerayInverseSectionHom i f M p
      naturality := fun {U V} g ↦ closedImmersionLerayInverse_naturality i f M p g }

/-- The forward Leray morphism followed by its sectionwise inverse is the identity. -/
theorem closedImmersionLerayComparison_hom_inv_id (M : Z.Modules) (p : ℕ) :
    closedImmersionLerayComparison i f M p ≫ closedImmersionLerayInverse i f M p =
      𝟙 _ := sorry

/-- The sectionwise inverse followed by the forward Leray morphism is the identity. -/
theorem closedImmersionLerayComparison_inv_hom_id (M : Z.Modules) (p : ℕ) :
    closedImmersionLerayInverse i f M p ≫ closedImmersionLerayComparison i f M p =
      𝟙 _ := sorry

/-- Higher direct image across a closed immersion is canonically computed after
its exact module pushforward. -/
def closedImmersionLerayIso (M : Z.Modules) (p : ℕ) :
    higherDirectImage (i ≫ f) M p ≅
      higherDirectImage f ((pushforward i).obj M) p where
  hom := closedImmersionLerayComparison i f M p
  inv := closedImmersionLerayInverse i f M p
  hom_inv_id := closedImmersionLerayComparison_hom_inv_id i f M p
  inv_hom_id := closedImmersionLerayComparison_inv_hom_id i f M p

end AlgebraicGeometry.AlgebraicSpace.Modules
