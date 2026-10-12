/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Homology.Additive
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.Algebra.Homology.HomotopyCategory.Shift
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Exact.Identity
public import ReasLib.CategoryTheory.DerivedCategory.Functor.TotalRightDerived
public import ReasLib.CategoryTheory.DerivedCategory.Functor.TotalRightDerived.Homotopy.Exact
public import stacks_project.Chap75.Lemma_75_10_2_Sequence
public import stacks_project.Chap75.Lemma_75_10_3_Composition

/-!
# Relative Mayer–Vietoris comparison maps for derived pushforward

An elementary distinguished square `(j : U ⟶ X, g : V ⟶ X)` and a morphism `f : X ⟶ Y`
determine comparison maps of derived direct image in `D(𝒪_Y)`, assembled into a triangle
whose vertices are `Rf_* E`, `Ra_*(E|_U) ⊞ Rb_*(E|_V)`, and `Rc_*(E|_{U ×_X V})`, where
`a = j ≫ f`, `b = g ≫ f`, and `c = fiberHom j g ≫ f`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules CategoryTheory.Limits
open CategoryTheory.Functor CategoryTheory.Pretriangulated ComplexShape
open AlgebraicGeometry.AlgebraicSpace.SmallEtaleModuleGlueing (restrictFunctorComp)

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

variable {S : Scheme.{u}}

/-- The structure morphism of an elementary distinguished square is étale. -/
instance etale_fiberHom {U V X : AlgebraicSpace S} (j : U ⟶ X) [Etale j]
    (g : V ⟶ X) [Etale g] : Etale (fiberHom j g) :=
  inferInstance

/-- Restriction to `U` followed by pushforward along `a = j ≫ f`. -/
abbrev along {U X Y : AlgebraicSpace S} (f : X ⟶ Y) (j : U ⟶ X) [Etale j] :
    X.Modules ⥤ Y.Modules :=
  restrictFunctor j ⋙ pushforward (j ≫ f)

/-- `along f j` is restriction along `j` followed by pushforward along `j ≫ f`. -/
theorem along_eq {U X Y : AlgebraicSpace S} (f : X ⟶ Y) (j : U ⟶ X) [Etale j] :
    along f j = restrictFunctor j ⋙ pushforward (j ≫ f) :=
  sorry

/-- The underived comparison `f_* ⟶ a_* ((-)|_U)` obtained from the étale unit of `j`
and `pushforwardCompIso j f`. -/
def alongUnit {U X Y : AlgebraicSpace S} (f : X ⟶ Y) (j : U ⟶ X) [Etale j] :
    pushforward f ⟶ along f j where
  app F :=
    (pushforward f).map ((restrictAdjunction j).unit.app F) ≫
      (pushforwardCompIso j f).hom.app (restrict F j)
  naturality := fun _ _ _ ↦ sorry

/-- `alongUnit` is pushforward of the étale unit of `j`, followed by `pushforwardCompIso`. -/
theorem alongUnit_eq {U X Y : AlgebraicSpace S} (f : X ⟶ Y) (j : U ⟶ X) [Etale j]
    (F : X.Modules) :
    (alongUnit f j).app F =
      (pushforward f).map ((restrictAdjunction j).unit.app F) ≫
        (pushforwardCompIso j f).hom.app (restrict F j) :=
  sorry

/-- Transport `along f p` along an equality of étale morphisms to `X`. -/
def alongObj_eq {W X Y : AlgebraicSpace S} {p q : W ⟶ X} [hp : Etale p] [hq : Etale q]
    (h : p = q) (f : X ⟶ Y) (F : X.Modules) :
    (along f p).obj F = (along f q).obj F :=
  Eq.rec (motive := fun r (_ : p = r) =>
      ∀ hr : Etale r,
        (@along S W X Y f p hp).obj F = (@along S W X Y f r hr).obj F)
    (fun hr =>
      congrArg (fun inst : Etale p => (@along S W X Y f p inst).obj F)
        (Subsingleton.elim hp hr))
    h hq

/-- The underived overlap comparison `a_* ((-)|_U) ⟶ a_W_* ((-)|_W)` along an étale
factorization `p : W ⟶ U`. -/
def alongRestriction {W U X Y : AlgebraicSpace S} (f : X ⟶ Y) (j : U ⟶ X) [Etale j]
    (p : W ⟶ U) [Etale p] :
    along f j ⟶ along f (p ≫ j) where
  app F :=
    (pushforward (j ≫ f)).map ((restrictAdjunction p).unit.app (restrict F j)) ≫
      (pushforwardCompIso p (j ≫ f)).hom.app ((restrictFunctor p).obj (restrict F j)) ≫
        (pushforward (p ≫ (j ≫ f))).map ((restrictFunctorComp p j).hom.app F) ≫
          eqToHom
            (congrArg (fun q => (pushforward q).obj ((restrictFunctor (p ≫ j)).obj F))
              (Category.assoc p j f).symm)
  naturality := fun _ _ _ ↦ sorry

/-- `alongRestriction` is the unit of `p` followed by `pushforwardCompIso p (j ≫ f)`. -/
theorem alongRestriction_eq {W U X Y : AlgebraicSpace S} (f : X ⟶ Y) (j : U ⟶ X)
    [Etale j] (p : W ⟶ U) [Etale p] (F : X.Modules) :
    (alongRestriction f j p).app F =
      (pushforward (j ≫ f)).map ((restrictAdjunction p).unit.app (restrict F j)) ≫
        (pushforwardCompIso p (j ≫ f)).hom.app ((restrictFunctor p).obj (restrict F j)) ≫
          (pushforward (p ≫ (j ≫ f))).map ((restrictFunctorComp p j).hom.app F) ≫
            eqToHom
              (congrArg (fun q => (pushforward q).obj ((restrictFunctor (p ≫ j)).obj F))
                (Category.assoc p j f).symm) :=
  sorry

/-- Homotopy-to-derived unit of the underived composite `along f j`. -/
def alongCompositeUnit {U X Y : AlgebraicSpace S} (f : X ⟶ Y) (j : U ⟶ X) [Etale j]
    [(restrictFunctor j).Additive] [(pushforward (j ≫ f)).Additive]
    [PreservesFiniteLimits (restrictFunctor j)]
    [PreservesFiniteColimits (restrictFunctor j)] :
    modulesMapHomotopy (restrictFunctor j) ⋙
        modulesHomotopyToDerived (pushforward (j ≫ f)) ⟶
      modulesQh X ⋙ modulesHomotopyFunctor (along f j) :=
  (associator
      (modulesMapHomotopy (restrictFunctor j))
      (modulesMapHomotopy (pushforward (j ≫ f)))
      (modulesQh Y)).hom ≫
    (isoWhiskerRight
        (mapHomotopyCategoryCompIso (Iso.refl (along f j)) (up ℤ))
        (modulesQh Y)).hom ≫
      modulesHomotopyUnit (along f j)

/-- The K-injective derived functor of `along f j` is a right-derived model of that
composite. -/
instance alongComposite_isRightDerived {U X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (j : U ⟶ X) [Etale j] [(restrictFunctor j).Additive]
    [(pushforward (j ≫ f)).Additive]
    [PreservesFiniteLimits (restrictFunctor j)]
    [PreservesFiniteColimits (restrictFunctor j)] :
    (modulesHomotopyFunctor (along f j)).IsRightDerivedFunctor
      (alongCompositeUnit f j)
      (@HomotopyCategory.quasiIso X.Modules _ ℤ (up ℤ) X.modulesAbelian.toPreadditive
        inferInstance) :=
  sorry

/-- Right-derived composition comparison `R(along f j) ⟶ (-)|_U ⋙ Ra_*`. -/
def alongDerivedComparison {U X Y : AlgebraicSpace S} (f : X ⟶ Y) (j : U ⟶ X)
    [Etale j] [(restrictFunctor j).Additive] [(pushforward (j ≫ f)).Additive]
    [PreservesFiniteLimits (restrictFunctor j)]
    [PreservesFiniteColimits (restrictFunctor j)] :
    modulesHomotopyFunctor (along f j) ⟶
      restrictFunctorDerived j ⋙ pushforwardDerived (j ≫ f) :=
  @RightDerived.Composition.comparisonOfModels
    (modulesHomotopy X) (modulesHomotopy U) (ModuleDerived Y)
    (ModuleDerived X) (ModuleDerived U)
    inferInstance inferInstance inferInstance inferInstance inferInstance
    (modulesMapHomotopy (restrictFunctor j))
    (modulesHomotopyToDerived (pushforward (j ≫ f)))
    (modulesQh X) (modulesQh U)
    (restrictFunctorDerived j) (pushforwardDerived (j ≫ f))
    (modulesHomotopyFunctor (along f j))
    (@HomotopyCategory.quasiIso X.Modules _ ℤ (up ℤ) X.modulesAbelian.toPreadditive
      inferInstance)
    (modulesRestrictFactorshInv j)
    (modulesHomotopyUnit (pushforward (j ≫ f)))
    (alongCompositeUnit f j)
    inferInstance inferInstance

/-- The composition comparison `R(along f j) ⟶ (-)|_U ⋙ Ra_*` is an isomorphism. -/
instance isIso_alongDerivedComparison {U X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (j : U ⟶ X) [Etale j] [(restrictFunctor j).Additive]
    [(pushforward (j ≫ f)).Additive]
    [PreservesFiniteLimits (restrictFunctor j)]
    [PreservesFiniteColimits (restrictFunctor j)] :
    IsIso (alongDerivedComparison f j) :=
  sorry

/-- Identification `R(along f j) ≅ (-)|_U ⋙ Ra_*` of derived functors. -/
def alongDerivedIso {U X Y : AlgebraicSpace S} (f : X ⟶ Y) (j : U ⟶ X) [Etale j]
    [(restrictFunctor j).Additive] [(pushforward (j ≫ f)).Additive]
    [PreservesFiniteLimits (restrictFunctor j)]
    [PreservesFiniteColimits (restrictFunctor j)] :
    modulesHomotopyFunctor (along f j) ≅
      restrictFunctorDerived j ⋙ pushforwardDerived (j ≫ f) :=
  asIso (alongDerivedComparison f j)

variable {U V X Y : AlgebraicSpace S} (f : X ⟶ Y) (j : U ⟶ X) [Etale j]
  (g : V ⟶ X) [Etale g]
variable [(restrictFunctor (fiberHom j g)).Additive]
variable [(restrictFunctor j).Additive]
variable [(restrictFunctor g).Additive]
variable [(pushforward f).Additive]
variable [(pushforward (j ≫ f)).Additive]
variable [(pushforward (g ≫ f)).Additive]
variable [(pushforward (fiberHom j g ≫ f)).Additive]
variable [PreservesFiniteLimits (restrictFunctor (fiberHom j g))]
variable [PreservesFiniteColimits (restrictFunctor (fiberHom j g))]
variable [PreservesFiniteLimits (restrictFunctor j)]
variable [PreservesFiniteColimits (restrictFunctor j)]
variable [PreservesFiniteLimits (restrictFunctor g)]
variable [PreservesFiniteColimits (restrictFunctor g)]

/-- The `V`-leg overlap restriction of `along`, transported along `fiberHom_eq`. -/
def alongRestriction_fiberHom :
    along f g ⟶ along f (fiberHom j g) where
  app F :=
    (alongRestriction f g (Limits.pullback.snd j g)).app F ≫
      eqToHom (alongObj_eq (fiberHom_eq j g).symm f F)
  naturality := fun _ _ _ ↦ sorry

/-- Derived `U`-leg unit `Rf_* E ⟶ Ra_*(E|_U)`. -/
def mayerVietorisRelativePushforwardιU (E : ModuleDerived X) :
    (pushforwardDerived f).obj E ⟶
      (pushforwardDerived (j ≫ f)).obj ((restrictFunctorDerived j).obj E) :=
  (Functor.RightDerived.Homotopy.mapNatTrans (alongUnit f j)).app E ≫
    (alongDerivedIso f j).hom.app E

/-- Derived `V`-leg unit `Rf_* E ⟶ Rb_*(E|_V)`. -/
def mayerVietorisRelativePushforwardιV (E : ModuleDerived X) :
    (pushforwardDerived f).obj E ⟶
      (pushforwardDerived (g ≫ f)).obj ((restrictFunctorDerived g).obj E) :=
  (Functor.RightDerived.Homotopy.mapNatTrans (alongUnit f g)).app E ≫
    (alongDerivedIso f g).hom.app E

/-- The first relative Mayer–Vietoris arrow
`Rf_* E ⟶ Ra_*(E|_U) ⊞ Rb_*(E|_V)`. -/
def mayerVietorisRelativePushforwardι (E : ModuleDerived X) :
    (pushforwardDerived f).obj E ⟶
      biprod ((pushforwardDerived (j ≫ f)).obj ((restrictFunctorDerived j).obj E))
        ((pushforwardDerived (g ≫ f)).obj ((restrictFunctorDerived g).obj E)) :=
  biprod.lift (mayerVietorisRelativePushforwardιU f j E)
    (mayerVietorisRelativePushforwardιV f g E)

/-- Derived `U`-leg overlap restriction `Ra_*(E|_U) ⟶ Rc_*(E|_W)`. -/
def mayerVietorisRelativePushforwardπU (E : ModuleDerived X) :
    (pushforwardDerived (j ≫ f)).obj ((restrictFunctorDerived j).obj E) ⟶
      (pushforwardDerived (fiberHom j g ≫ f)).obj
        ((restrictFunctorDerived (fiberHom j g)).obj E) :=
  (alongDerivedIso f j).inv.app E ≫
    (Functor.RightDerived.Homotopy.mapNatTrans
      (alongRestriction f j (Limits.pullback.fst j g))).app E ≫
    (alongDerivedIso f (fiberHom j g)).hom.app E

/-- Derived `V`-leg overlap restriction `Rb_*(E|_V) ⟶ Rc_*(E|_W)`. -/
def mayerVietorisRelativePushforwardπV (E : ModuleDerived X) :
    (pushforwardDerived (g ≫ f)).obj ((restrictFunctorDerived g).obj E) ⟶
      (pushforwardDerived (fiberHom j g ≫ f)).obj
        ((restrictFunctorDerived (fiberHom j g)).obj E) :=
  (alongDerivedIso f g).inv.app E ≫
    (Functor.RightDerived.Homotopy.mapNatTrans
      (alongRestriction_fiberHom f j g)).app E ≫
    (alongDerivedIso f (fiberHom j g)).hom.app E

/-- The second relative Mayer–Vietoris arrow
`Ra_*(E|_U) ⊞ Rb_*(E|_V) ⟶ Rc_*(E|_W)`, with a sign on the `V`-leg. -/
def mayerVietorisRelativePushforwardπ (E : ModuleDerived X) :
    biprod ((pushforwardDerived (j ≫ f)).obj ((restrictFunctorDerived j).obj E))
        ((pushforwardDerived (g ≫ f)).obj ((restrictFunctorDerived g).obj E)) ⟶
      (pushforwardDerived (fiberHom j g ≫ f)).obj
        ((restrictFunctorDerived (fiberHom j g)).obj E) :=
  biprod.desc (mayerVietorisRelativePushforwardπU f j g E)
    (-mayerVietorisRelativePushforwardπV f j g E)

/-- The cochain-level first relative Mayer–Vietoris arrow. -/
def mayerVietorisRelativePushforwardCochainι (K : CochainComplex X.Modules ℤ) :
    ((pushforward f).mapHomologicalComplex (up ℤ)).obj K ⟶
      biprod (((along f j).mapHomologicalComplex (up ℤ)).obj K)
        (((along f g).mapHomologicalComplex (up ℤ)).obj K) :=
  biprod.lift
    ((NatTrans.mapHomologicalComplex (alongUnit f j) (up ℤ)).app K)
    ((NatTrans.mapHomologicalComplex (alongUnit f g) (up ℤ)).app K)

/-- The cochain-level second relative Mayer–Vietoris arrow. -/
def mayerVietorisRelativePushforwardCochainπ (K : CochainComplex X.Modules ℤ) :
    biprod (((along f j).mapHomologicalComplex (up ℤ)).obj K)
        (((along f g).mapHomologicalComplex (up ℤ)).obj K) ⟶
      ((along f (fiberHom j g)).mapHomologicalComplex (up ℤ)).obj K :=
  biprod.desc
    ((NatTrans.mapHomologicalComplex
      (alongRestriction f j (Limits.pullback.fst j g)) (up ℤ)).app K)
    (-(NatTrans.mapHomologicalComplex (alongRestriction_fiberHom f j g) (up ℤ)).app K)

/-- The short complex of cochain complexes obtained by applying the module-level
relative Mayer–Vietoris arrows degreewise. -/
def mayerVietorisRelativePushforwardCochainShortComplex
    (K : CochainComplex X.Modules ℤ) :
    ShortComplex (CochainComplex Y.Modules ℤ) :=
  ShortComplex.mk (mayerVietorisRelativePushforwardCochainι f j g K)
    (mayerVietorisRelativePushforwardCochainπ f j g K) sorry

variable [IsElementaryDistinguishedSquare j g]

/-- The cochain-level relative Mayer–Vietoris sequence is short exact on complexes
with injective terms, using `R¹ f_* I = 0`. -/
theorem mayerVietorisRelativePushforwardCochain_shortExact
    (K : CochainComplex X.Modules ℤ) [∀ n, Injective (K.X n)] :
    (mayerVietorisRelativePushforwardCochainShortComplex f j g K).ShortExact :=
  sorry

/-- Cochain-level connecting map of the relative Mayer–Vietoris short exact sequence on a
complex with injective terms. -/
def mayerVietorisRelativePushforwardδCochain
    (K : CochainComplex X.Modules ℤ) [∀ n, Injective (K.X n)] :
    DerivedCategory.Q.obj
        (((along f (fiberHom j g)).mapHomologicalComplex (up ℤ)).obj K) ⟶
      DerivedCategory.Q.obj
          (((pushforward f).mapHomologicalComplex (up ℤ)).obj K)⟦(1 : ℤ)⟧ :=
  DerivedCategory.triangleOfSESδ
    (mayerVietorisRelativePushforwardCochain_shortExact f j g K)

/-- On a K-injective complex, `f_*` computes `Rf_*`. -/
theorem isIso_mayerVietorisRelativePushforward_unit_app
    (K : CochainComplex X.Modules ℤ) [K.IsKInjective] :
    IsIso ((Functor.RightDerived.KInjective.unit.{u} (pushforward f)).app K) :=
  sorry

/-- On a K-injective termwise-injective complex, the cochain connecting map lands in `Rf_*`
after the K-injective unit. -/
def mayerVietorisRelativePushforwardδCochain_kInjective
    (K : CochainComplex X.Modules ℤ) [K.IsKInjective] [∀ n, Injective (K.X n)] :
    DerivedCategory.Q.obj
        (((along f (fiberHom j g)).mapHomologicalComplex (up ℤ)).obj K) ⟶
      ((pushforwardDerived f).obj (DerivedCategory.Q.obj K))⟦(1 : ℤ)⟧ :=
  mayerVietorisRelativePushforwardδCochain f j g K ≫
    ((Functor.RightDerived.KInjective.unit.{u} (pushforward f)).app K)⟦(1 : ℤ)⟧'

/-- Underived identification of restriction-then-étale-pushforward followed by `f_*`
with `along f (fiberHom j g)`. -/
def alongCompIso :
    (restrictFunctor (fiberHom j g) ⋙ pushforward (fiberHom j g)) ⋙ pushforward f ≅
      along f (fiberHom j g) :=
  Functor.associator (restrictFunctor (fiberHom j g))
      (pushforward (fiberHom j g)) (pushforward f) ≪≫
    isoWhiskerLeft (restrictFunctor (fiberHom j g)) (pushforwardCompIso (fiberHom j g) f)

/-- `alongCompIso` is the associator of `restrictFunctor` followed by `pushforwardCompIso`. -/
theorem alongCompIso_eq :
    alongCompIso f j g =
      Functor.associator (restrictFunctor (fiberHom j g))
          (pushforward (fiberHom j g)) (pushforward f) ≪≫
        isoWhiskerLeft (restrictFunctor (fiberHom j g))
          (pushforwardCompIso (fiberHom j g) f) :=
  sorry

/-- Cochain-level connecting maps into `Rf_* ((-)⟦1⟧)`, obtained from the identity-base
Mayer–Vietoris `triangleOfSESδ` and `pushforwardCompIso`. This NatTrans is the
`rightDerivedDesc` input; it agrees with `δCochain` after the K-injective unit on
termwise-injective K-injective complexes. -/
def mayerVietorisRelativePushforwardδCochainNatTrans :
    (along f (fiberHom j g)).mapHomologicalComplex (up ℤ) ⋙
        (DerivedCategory.Q : CochainComplex Y.Modules ℤ ⥤ ModuleDerived Y) ⟶
      (DerivedCategory.Q : CochainComplex X.Modules ℤ ⥤ ModuleDerived X) ⋙
        shiftFunctor (ModuleDerived X) (1 : ℤ) ⋙ pushforwardDerived f where
  app K :=
    DerivedCategory.Q.map
        ((Functor.mapHomologicalComplexCompIso (alongCompIso f j g) (up ℤ)).inv.app K) ≫
      (Functor.RightDerived.KInjective.unit.{u} (pushforward f)).app
        (((restrictFunctor (fiberHom j g) ⋙
            pushforward (fiberHom j g)).mapHomologicalComplex (up ℤ)).obj K) ≫
      (pushforwardDerived f).map ((mayerVietorisPushforwardδCochain j g).app K)
  naturality := fun _ _ _ ↦ sorry

/-- The K-injective derived functor of the overlap composite `along f (fiberHom j g)` is a
cochain-level right-derived model. -/
instance mayerVietorisRelativePushforward_overlapComposite_isRightDerived :
    (Functor.RightDerived.KInjective.functor.{u} (along f (fiberHom j g))).IsRightDerivedFunctor
      (Functor.RightDerived.KInjective.unit.{u} (along f (fiberHom j g)))
      (HomologicalComplex.quasiIso X.Modules (up ℤ)) :=
  sorry

/-- Whiskered cochain unit exhibiting `Rf_* ⋙ ((-)⟦1⟧)` as a right-derived functor. -/
def pushforwardDerived_shiftWhiskerUnit :
    (pushforward f).mapHomologicalComplex (up ℤ) ⋙
        (DerivedCategory.Q : CochainComplex Y.Modules ℤ ⥤ ModuleDerived Y) ⋙
          shiftFunctor (ModuleDerived Y) (1 : ℤ) ⟶
      (DerivedCategory.Q : CochainComplex X.Modules ℤ ⥤ ModuleDerived X) ⋙
        pushforwardDerived f ⋙ shiftFunctor (ModuleDerived Y) (1 : ℤ) :=
  whiskerRight (Functor.RightDerived.KInjective.unit.{u} (pushforward f))
    (shiftFunctor (ModuleDerived Y) (1 : ℤ))

/-- `Rf_* ⋙ ((-)⟦1⟧)` is a cochain-level right-derived model of `f_*`. -/
instance pushforwardDerived_shiftWhisker_isRightDerived :
    (pushforwardDerived f ⋙ shiftFunctor (ModuleDerived Y) (1 : ℤ)).IsRightDerivedFunctor
      (pushforwardDerived_shiftWhiskerUnit f)
      (HomologicalComplex.quasiIso X.Modules (up ℤ)) :=
  sorry

/-- Cochain-level unit exhibiting `((-)⟦1⟧) ⋙ Rf_*` as a right-derived functor. -/
def pushforwardDerived_shiftSourceUnit :
    (pushforward f).mapHomologicalComplex (up ℤ) ⋙
        shiftFunctor (CochainComplex Y.Modules ℤ) (1 : ℤ) ⋙
          (DerivedCategory.Q : CochainComplex Y.Modules ℤ ⥤ ModuleDerived Y) ⟶
      (DerivedCategory.Q : CochainComplex X.Modules ℤ ⥤ ModuleDerived X) ⋙
        shiftFunctor (ModuleDerived X) (1 : ℤ) ⋙ pushforwardDerived f where
  app K :=
    DerivedCategory.Q.map
        (((pushforward f).mapCochainComplexShiftIso (1 : ℤ)).inv.app K) ≫
      (Functor.RightDerived.KInjective.unit.{u} (pushforward f)).app (K⟦(1 : ℤ)⟧) ≫
      (pushforwardDerived f).map
        (((DerivedCategory.Q : CochainComplex X.Modules ℤ ⥤ ModuleDerived X).commShiftIso
            (1 : ℤ)).hom.app K)
  naturality := fun _ _ _ ↦ sorry

/-- `((-)⟦1⟧) ⋙ Rf_*` is a cochain-level right-derived model of `f_*`. -/
instance pushforwardDerived_shiftSource_isRightDerived :
    (shiftFunctor (ModuleDerived X) (1 : ℤ) ⋙ pushforwardDerived f).IsRightDerivedFunctor
      (pushforwardDerived_shiftSourceUnit f)
      (HomologicalComplex.quasiIso X.Modules (up ℤ)) :=
  sorry

/-- `Rf_*` commutes with the shift `[1]`. -/
def pushforwardDerived_commShiftIso1 :
    shiftFunctor (ModuleDerived X) (1 : ℤ) ⋙ pushforwardDerived f ≅
      pushforwardDerived f ⋙ shiftFunctor (ModuleDerived Y) (1 : ℤ) :=
  Functor.RightDerived.natIsoOfIso
    (DerivedCategory.Q : CochainComplex X.Modules ℤ ⥤ ModuleDerived X)
    (HomologicalComplex.quasiIso X.Modules (up ℤ))
    (pushforwardDerived_shiftSourceUnit f) (pushforwardDerived_shiftWhiskerUnit f)
    (isoWhiskerLeft ((pushforward f).mapHomologicalComplex (up ℤ))
      ((DerivedCategory.Q : CochainComplex Y.Modules ℤ ⥤ ModuleDerived Y).commShiftIso
        (1 : ℤ)))

/-- Connecting morphism of derived functors, obtained by descending the cochain-level
connecting NatTrans along the K-injective unit of the overlap composite. -/
def mayerVietorisRelativePushforwardδNatTrans :
    Functor.RightDerived.Homotopy.functor (along f (fiberHom j g)) ⟶
      shiftFunctor (ModuleDerived X) (1 : ℤ) ⋙ pushforwardDerived f :=
  (Functor.RightDerived.KInjective.functor.{u} (along f (fiberHom j g))).rightDerivedDesc
    (Functor.RightDerived.KInjective.unit.{u} (along f (fiberHom j g)))
    (HomologicalComplex.quasiIso X.Modules (up ℤ))
    (shiftFunctor (ModuleDerived X) (1 : ℤ) ⋙ pushforwardDerived f)
    (mayerVietorisRelativePushforwardδCochainNatTrans f j g)

/-- On a K-injective termwise-injective complex, the descended connecting map agrees with
`triangleOfSESδ` of the guarded relative short exact sequence after the K-injective unit. -/
theorem mayerVietorisRelativePushforwardδCochain_kInjective_eq
    (K : CochainComplex X.Modules ℤ) [K.IsKInjective] [∀ n, Injective (K.X n)] :
    mayerVietorisRelativePushforwardδCochain_kInjective f j g K =
      (mayerVietorisRelativePushforwardδCochainNatTrans f j g).app K ≫
        (pushforwardDerived_commShiftIso1 f).hom.app (DerivedCategory.Q.obj K) :=
  sorry

/-- The connecting morphism of the relative Mayer–Vietoris triangle in `D(𝒪_Y)`. -/
def mayerVietorisRelativePushforwardδ (E : ModuleDerived X) :
    (pushforwardDerived (fiberHom j g ≫ f)).obj
      ((restrictFunctorDerived (fiberHom j g)).obj E) ⟶
      ((pushforwardDerived f).obj E)⟦(1 : ℤ)⟧ :=
  (alongDerivedIso f (fiberHom j g)).inv.app E ≫
    (mayerVietorisRelativePushforwardδNatTrans f j g).app E ≫
    (pushforwardDerived_commShiftIso1 f).hom.app E

/-- The relative Mayer–Vietoris distinguished-triangle data of derived pushforward in
`D(𝒪_Y)`. -/
def mayerVietorisRelativePushforwardTriangle (E : ModuleDerived X) :
    Triangle (ModuleDerived Y) :=
  Triangle.mk (mayerVietorisRelativePushforwardι f j g E)
    (mayerVietorisRelativePushforwardπ f j g E)
    (mayerVietorisRelativePushforwardδ f j g E)

/-- The first vertex of the relative Mayer–Vietoris triangle is `Rf_* E`. -/
theorem mayerVietorisRelativePushforwardTriangle_obj₁ (E : ModuleDerived X) :
    (mayerVietorisRelativePushforwardTriangle f j g E).obj₁ =
      (pushforwardDerived f).obj E :=
  sorry

/-- The second vertex of the relative Mayer–Vietoris triangle is
`Ra_*(E|_U) ⊞ Rb_*(E|_V)`. -/
theorem mayerVietorisRelativePushforwardTriangle_obj₂ (E : ModuleDerived X) :
    (mayerVietorisRelativePushforwardTriangle f j g E).obj₂ =
      biprod ((pushforwardDerived (j ≫ f)).obj ((restrictFunctorDerived j).obj E))
        ((pushforwardDerived (g ≫ f)).obj ((restrictFunctorDerived g).obj E)) :=
  sorry

/-- The third vertex of the relative Mayer–Vietoris triangle is `Rc_*(E|_{U ×_X V})`. -/
theorem mayerVietorisRelativePushforwardTriangle_obj₃ (E : ModuleDerived X) :
    (mayerVietorisRelativePushforwardTriangle f j g E).obj₃ =
      (pushforwardDerived (fiberHom j g ≫ f)).obj
        ((restrictFunctorDerived (fiberHom j g)).obj E) :=
  sorry

/-- The relative Mayer–Vietoris triangle as a functor of `E` in `D(𝒪_X)`. -/
def mayerVietorisRelativePushforwardTriangleFunctor :
    ModuleDerived X ⥤ Triangle (ModuleDerived Y) where
  obj E := mayerVietorisRelativePushforwardTriangle f j g E
  map {E E'} φ :=
    Triangle.homMk (mayerVietorisRelativePushforwardTriangle f j g E)
      (mayerVietorisRelativePushforwardTriangle f j g E')
      ((pushforwardDerived f).map φ)
      (biprod.map
        ((pushforwardDerived (j ≫ f)).map ((restrictFunctorDerived j).map φ))
        ((pushforwardDerived (g ≫ f)).map ((restrictFunctorDerived g).map φ)))
      ((pushforwardDerived (fiberHom j g ≫ f)).map
        ((restrictFunctorDerived (fiberHom j g)).map φ))
      sorry sorry sorry
  map_id := sorry
  map_comp := sorry

/-- The triangle functor evaluates at `E` as `mayerVietorisRelativePushforwardTriangle`. -/
theorem mayerVietorisRelativePushforwardTriangleFunctor_obj_eq (E : ModuleDerived X) :
    (mayerVietorisRelativePushforwardTriangleFunctor f j g).obj E =
      mayerVietorisRelativePushforwardTriangle f j g E :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules
