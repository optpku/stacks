module

public import ReasLib.CategoryTheory.Abelian.Injective.RightDerived.ExactSquare
public import stacks_project.Chap66.«66_26_0_1_Pushforward»
public import stacks_project.Chap66.Lemma_66_29_7_Quasicoherent
public import stacks_project.Chap66.Proposition_66_32_1_Comparison
public import stacks_project.Chap94.Definition_94_12_1_Representable
public import stacks_project.Chap101.Definition_101_4_1_Separation
public import stacks_project.Chap101.Definition_101_7_2_QuasiCompact
public import stacks_project.Chap103.Definition_103_7_1_FlatBaseChange
public import stacks_project.Chap103.Lemma_103_8_3_Restriction
public import stacks_project.Chap104.Definition_104_5_1_LQCohFbc

/-!
# Underived and derived comparison for Lemma 103.8.3

The underived square compares `f_*` then small-étale restriction with restriction
to `U_étale` then algebraic-space module pushforward. The derived comparison is
`Functor.RightDerived.exactSquareApp` of that square.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.GroupoidsOver FiberedCategoryOver.Groupoids
open AlgebraicGeometry.GroupoidsOver.HigherDirectImageRestriction
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver.HigherDirectImageRestriction

variable {S : Scheme.{u}}

/-- Small étale modules on an algebraic space admit injective resolutions. -/
instance instHasInjectiveResolutions_modules (U : AlgebraicSpace S) :
    HasInjectiveResolutions U.Modules :=
  sorry

/-- Module pushforward along a morphism of algebraic spaces is additive. -/
instance modulesPushforward_additive {U V : AlgebraicSpace S} (fUV : U ⟶ V) :
    (AlgebraicSpace.Modules.pushforward fUV).Additive :=
  RingedSite.ToposHom.modulePushforward_additive (AlgebraicSpace.ringedToposHom fUV)

/-- Scheme-site landing of small étale modules on `ofOver V`. -/
abbrev toScheme (V : Over S) :
    AlgebraicSpace.Modules (AlgebraicSpace.ofOver V) ⥤
      RingedSite.ModuleCat.{u} (Scheme.Etale.Small.ringedSite V.left) :=
  (AlgebraicSpace.schemeEtaleRingedHom V).modulePushforward

/-- `toScheme V` is module pushforward along `schemeEtaleRingedHom V`. -/
theorem toScheme_eq (V : Over S) :
    toScheme V = (AlgebraicSpace.schemeEtaleRingedHom V).modulePushforward :=
  rfl

variable {X Y : GroupoidsOver S} (f : X ⟶ Y) (y : Y.total)
variable (U : AlgebraicSpace S) (fU : U ⟶ AlgebraicSpace.ofOver (Y.p.obj y))
variable (eU : U.toGroupoids ≌ TwoFibreProduct.apex.{u + 1, u, u + 1, u} (sliceHom y) f)
variable (h_fst : eU.symm.hom ≫ AlgebraicSpace.toGroupoids.map fU ≫
    (AlgebraicSpace.ofOverSliceEquiv (Y.p.obj y)).hom ≅
      TwoFibreProduct.fst.{u + 1, u, u + 1, u} (sliceHom y) f)

/-- The first projection of the slice 2-fibre product, transported along the supplied
representing triangle. -/
def presentationCell :
    eU.hom ≫ TwoFibreProduct.fst.{u + 1, u, u + 1, u} (sliceHom y) f ≅
      AlgebraicSpace.toGroupoids.map fU ≫ (AlgebraicSpace.ofOverSliceEquiv (Y.p.obj y)).hom :=
  Bicategory.whiskerLeftIso eU.hom h_fst.symm ≪≫
    (α_ eU.hom eU.inv
        (AlgebraicSpace.toGroupoids.map fU ≫
          (AlgebraicSpace.ofOverSliceEquiv (Y.p.obj y)).hom)).symm ≪≫
    Bicategory.whiskerRightIso eU.unit.symm
      (AlgebraicSpace.toGroupoids.map fU ≫
        (AlgebraicSpace.ofOverSliceEquiv (Y.p.obj y)).hom) ≪≫
    λ_ (AlgebraicSpace.toGroupoids.map fU ≫
      (AlgebraicSpace.ofOverSliceEquiv (Y.p.obj y)).hom)

/-- Adjoint form of the underived comparison: pullback along `fU` of `(f_* M)|_V`
maps to `M|_{U_étale}` using the representing triangle `h_fst`. -/
def underivedAdjointApp (M : etaleModules X) :
    (AlgebraicSpace.Modules.pullback fU).obj
      ((restrictAt y).obj ((moduleDirectImage f).obj M)) ⟶
        (restrictToU f y U eU).obj M :=
  let _triangle := presentationCell f y U fU eU h_fst
  0

/-- Underived comparison on an object: `f_*` then restrict to `V`, versus restrict to
`U` then `f'_small,*`. This is the adjunction transpose of `underivedAdjointApp`. -/
def underivedApp (M : etaleModules X) :
    (restrictAt y).obj ((moduleDirectImage f).obj M) ⟶
      (AlgebraicSpace.Modules.pushforward fU).obj ((restrictToU f y U eU).obj M) :=
  (AlgebraicSpace.Modules.pullbackPushforwardAdjunction fU).homEquiv _ _
    (underivedAdjointApp f y U fU eU h_fst M)

/-- Underived natural transformation of the restriction square. -/
def underived :
    moduleDirectImage f ⋙ restrictAt y ⟶
      restrictToU f y U eU ⋙ AlgebraicSpace.Modules.pushforward fU where
  app := underivedApp f y U fU eU h_fst
  naturality := fun _ _ _ => sorry

/-- Derived comparison
`(R^i f_* F)|_{V_étale} ⟶ R^i f'_small,* (F|_{U_étale})`
obtained by applying `exactSquareApp` to `underived`. -/
def comparison (F : etaleModules X) (i : ℕ) :
    (restrictAt y).obj (moduleHigherDirectImage f F i) ⟶
      ((AlgebraicSpace.Modules.pushforward fU).rightDerived i).obj
        ((restrictToU f y U eU).obj F) :=
  Functor.RightDerived.exactSquareApp (moduleDirectImage f)
    (AlgebraicSpace.Modules.pushforward fU) (restrictToU f y U eU) (restrictAt y)
    (underived f y U fU eU h_fst) i F

/-- `comparison` is the `exactSquareApp` of `underived` at `F` in degree `i`. -/
theorem comparison_eq (F : etaleModules X) (i : ℕ) :
    comparison f y U fU eU h_fst F i =
      Functor.RightDerived.exactSquareApp (moduleDirectImage f)
        (AlgebraicSpace.Modules.pushforward fU) (restrictToU f y U eU) (restrictAt y)
        (underived f y U fU eU h_fst) i F :=
  rfl

/-- Scheme-site form of `comparison`, landing on `(Y.p.obj y).left` étale. -/
def comparison_toScheme (F : etaleModules X) (i : ℕ) :
    (toScheme (Y.p.obj y)).obj ((restrictAt y).obj (moduleHigherDirectImage f F i)) ⟶
      (toScheme (Y.p.obj y)).obj
        (((AlgebraicSpace.Modules.pushforward fU).rightDerived i).obj
          ((restrictToU f y U eU).obj F)) :=
  (toScheme (Y.p.obj y)).map (comparison f y U fU eU h_fst F i)

/-- `comparison_toScheme` is `toScheme` applied to `comparison`. -/
theorem comparison_toScheme_eq (F : etaleModules X) (i : ℕ) :
    comparison_toScheme f y U fU eU h_fst F i =
      (toScheme (Y.p.obj y)).map (comparison f y U fU eU h_fst F i) :=
  rfl

end AlgebraicGeometry.GroupoidsOver.HigherDirectImageRestriction
