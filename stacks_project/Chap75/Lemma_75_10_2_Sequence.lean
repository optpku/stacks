module

public import Mathlib.Algebra.Homology.Additive
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Exact.Identity
public import ReasLib.CategoryTheory.DerivedCategory.Functor.TotalRightDerived
public import ReasLib.CategoryTheory.DerivedCategory.Functor.TotalRightDerived.Homotopy.Exact
public import stacks_project.Chap66.Lemma_66_26_3_Glueing
public import stacks_project.Chap75.Lemma_75_10_1_Sequence
public import stacks_project.Chap75.Lemma_75_3_1_Comparison
public import stacks_project.Chap75.Lemma_75_3_1_Pushforward

/-!
# Mayer–Vietoris comparison maps for étale pushforward

An elementary distinguished square `(j : U ⟶ X, f : V ⟶ X)` determines comparison
maps of étale direct image of an `𝒪_X`-module along the three legs, assembled into a
short complex and into a triangle in `D(𝒪_X)`.
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

/-- Transport `j_* F|_U` along an equality of étale morphisms to `X`. -/
def pushforwardRestrictObj_eq {W X : AlgebraicSpace S} {p q : W ⟶ X}
    [hp : Etale p] [hq : Etale q] (h : p = q) (F : X.Modules) :
    (pushforward p).obj (restrict F p) = (pushforward q).obj (restrict F q) :=
  Eq.rec (motive := fun r (_ : p = r) =>
      ∀ hr : Etale r,
        (@pushforward S W X p).obj (@restrict S W X F p hp) =
          (@pushforward S W X r).obj (@restrict S W X F r hr))
    (fun hr =>
      congrArg (fun inst : Etale p =>
          (@pushforward S W X p).obj (@restrict S W X F p inst))
        (Subsingleton.elim hp hr))
    h hq

/-- The comparison `j_* F|_U ⟶ j_{W*} F|_W` of étale pushforward along a factorization
`W ⟶ U ⟶ X`. -/
def pushforwardRestrictHom {W U X : AlgebraicSpace S} (p : W ⟶ U) [Etale p]
    (j : U ⟶ X) [Etale j] (F : X.Modules) :
    (pushforward j).obj (restrict F j) ⟶
      (pushforward (p ≫ j)).obj (restrict F (p ≫ j)) :=
  ((restrictAdjunction (p ≫ j)).homEquiv
      ((pushforward j).obj (restrict F j)) (restrict F (p ≫ j)))
    ((restrictFunctorComp p j).inv.app ((pushforward j).obj (restrict F j)) ≫
      (restrictFunctor p).map ((restrictAdjunction j).counit.app (restrict F j)) ≫
      (restrictFunctorComp p j).hom.app F)

/-- `pushforwardRestrictHom` is the adjunct of the restricted counit of
`restrictAdjunction j`, after identifying successive restrictions with restriction
along the composite. -/
theorem pushforwardRestrictHom_eq {W U X : AlgebraicSpace S} (p : W ⟶ U) [Etale p]
    (j : U ⟶ X) [Etale j] (F : X.Modules) :
    pushforwardRestrictHom p j F =
      ((restrictAdjunction (p ≫ j)).homEquiv
          ((pushforward j).obj (restrict F j)) (restrict F (p ≫ j)))
        ((restrictFunctorComp p j).inv.app ((pushforward j).obj (restrict F j)) ≫
          (restrictFunctor p).map ((restrictAdjunction j).counit.app (restrict F j)) ≫
          (restrictFunctorComp p j).hom.app F) :=
  sorry

/-- The `U`-leg unit of the Mayer–Vietoris pushforward comparison. -/
def mayerVietorisPushforwardιU {U V X : AlgebraicSpace S} (j : U ⟶ X) [Etale j]
    (f : V ⟶ X) [Etale f] (F : X.Modules) :
    F ⟶ (pushforward j).obj (restrict F j) :=
  (restrictAdjunction j).unit.app F

/-- The `V`-leg unit of the Mayer–Vietoris pushforward comparison. -/
def mayerVietorisPushforwardιV {U V X : AlgebraicSpace S} (j : U ⟶ X) [Etale j]
    (f : V ⟶ X) [Etale f] (F : X.Modules) :
    F ⟶ (pushforward f).obj (restrict F f) :=
  (restrictAdjunction f).unit.app F

/-- The first Mayer–Vietoris arrow
`F ⟶ j_{U,*} F|_U ⊞ j_{V,*} F|_V`. -/
def mayerVietorisPushforwardι {U V X : AlgebraicSpace S} (j : U ⟶ X) [Etale j]
    (f : V ⟶ X) [Etale f] (F : X.Modules) :
    F ⟶ biprod ((pushforward j).obj (restrict F j)) ((pushforward f).obj (restrict F f)) :=
  biprod.lift (mayerVietorisPushforwardιU j f F) (mayerVietorisPushforwardιV j f F)

/-- The `U`-leg overlap restriction of the Mayer–Vietoris pushforward comparison. -/
def mayerVietorisPushforwardπU {U V X : AlgebraicSpace S} (j : U ⟶ X) [Etale j]
    (f : V ⟶ X) [Etale f] (F : X.Modules) :
    (pushforward j).obj (restrict F j) ⟶
      (pushforward (fiberHom j f)).obj (restrict F (fiberHom j f)) :=
  pushforwardRestrictHom (Limits.pullback.fst j f) j F

/-- The `V`-leg overlap restriction of the Mayer–Vietoris pushforward comparison,
transported along `fiberHom_eq`. -/
def mayerVietorisPushforwardπV {U V X : AlgebraicSpace S} (j : U ⟶ X) [Etale j]
    (f : V ⟶ X) [Etale f] (F : X.Modules) :
    (pushforward f).obj (restrict F f) ⟶
      (pushforward (fiberHom j f)).obj (restrict F (fiberHom j f)) :=
  pushforwardRestrictHom (Limits.pullback.snd j f) f F ≫
    eqToHom (pushforwardRestrictObj_eq (fiberHom_eq j f).symm F)

/-- The second Mayer–Vietoris arrow
`j_{U,*} F|_U ⊞ j_{V,*} F|_V ⟶ j_{U×_X V,*} F|_{U×_X V}`, with a sign on the `V`-leg. -/
def mayerVietorisPushforwardπ {U V X : AlgebraicSpace S} (j : U ⟶ X) [Etale j]
    (f : V ⟶ X) [Etale f] (F : X.Modules) :
    biprod ((pushforward j).obj (restrict F j)) ((pushforward f).obj (restrict F f)) ⟶
      (pushforward (fiberHom j f)).obj (restrict F (fiberHom j f)) :=
  biprod.desc (mayerVietorisPushforwardπU j f F) (-mayerVietorisPushforwardπV j f F)

/-- The three-term complex of étale pushforward along an elementary distinguished square. -/
def mayerVietorisPushforwardShortComplex {U V X : AlgebraicSpace S} (j : U ⟶ X)
    [Etale j] (f : V ⟶ X) [Etale f] (F : X.Modules) : ShortComplex X.Modules :=
  ShortComplex.mk (mayerVietorisPushforwardι j f F) (mayerVietorisPushforwardπ j f F) sorry

/-- The left vertex of the Mayer–Vietoris short complex is `F`. -/
theorem mayerVietorisPushforwardShortComplex_X₁ {U V X : AlgebraicSpace S}
    (j : U ⟶ X) [Etale j] (f : V ⟶ X) [Etale f] (F : X.Modules) :
    (mayerVietorisPushforwardShortComplex j f F).X₁ = F :=
  sorry

/-- The middle vertex of the Mayer–Vietoris short complex is
`j_{U,*} F|_U ⊞ j_{V,*} F|_V`. -/
theorem mayerVietorisPushforwardShortComplex_X₂ {U V X : AlgebraicSpace S}
    (j : U ⟶ X) [Etale j] (f : V ⟶ X) [Etale f] (F : X.Modules) :
    (mayerVietorisPushforwardShortComplex j f F).X₂ =
      biprod ((pushforward j).obj (restrict F j)) ((pushforward f).obj (restrict F f)) :=
  sorry

/-- The right vertex of the Mayer–Vietoris short complex is
`j_{U×_X V,*} F|_{U×_X V}`. -/
theorem mayerVietorisPushforwardShortComplex_X₃ {U V X : AlgebraicSpace S}
    (j : U ⟶ X) [Etale j] (f : V ⟶ X) [Etale f] (F : X.Modules) :
    (mayerVietorisPushforwardShortComplex j f F).X₃ =
      (pushforward (fiberHom j f)).obj (restrict F (fiberHom j f)) :=
  sorry

/-- The first arrow of the Mayer–Vietoris short complex is `mayerVietorisPushforwardι`. -/
theorem mayerVietorisPushforwardShortComplex_f {U V X : AlgebraicSpace S}
    (j : U ⟶ X) [Etale j] (f : V ⟶ X) [Etale f] (F : X.Modules) :
    (mayerVietorisPushforwardShortComplex j f F).f = mayerVietorisPushforwardι j f F :=
  sorry

/-- The second arrow of the Mayer–Vietoris short complex is `mayerVietorisPushforwardπ`. -/
theorem mayerVietorisPushforwardShortComplex_g {U V X : AlgebraicSpace S}
    (j : U ⟶ X) [Etale j] (f : V ⟶ X) [Etale f] (F : X.Modules) :
    (mayerVietorisPushforwardShortComplex j f F).g = mayerVietorisPushforwardπ j f F :=
  sorry

/-- The `U`-leg unit as a natural transformation `𝟭 ⟶ j_* j^*`. -/
def mayerVietorisPushforwardιNatTransU {U X : AlgebraicSpace S} (j : U ⟶ X)
    [Etale j] :
    𝟭 X.Modules ⟶ restrictFunctor j ⋙ pushforward j :=
  (restrictAdjunction j).unit

/-- The `V`-leg unit as a natural transformation `𝟭 ⟶ f_* f^*`. -/
def mayerVietorisPushforwardιNatTransV {V X : AlgebraicSpace S} (f : V ⟶ X)
    [Etale f] :
    𝟭 X.Modules ⟶ restrictFunctor f ⋙ pushforward f :=
  (restrictAdjunction f).unit

/-- The `U`-leg overlap restriction as a natural transformation of étale pushforwards
on `X`. -/
def mayerVietorisPushforwardπNatTransU {U V X : AlgebraicSpace S} (j : U ⟶ X)
    [Etale j] (f : V ⟶ X) [Etale f] :
    restrictFunctor j ⋙ pushforward j ⟶
      restrictFunctor (fiberHom j f) ⋙ pushforward (fiberHom j f) where
  app F := mayerVietorisPushforwardπU j f F
  naturality := fun _ _ _ ↦ sorry

/-- The `V`-leg overlap restriction as a natural transformation of étale pushforwards
on `X`. -/
def mayerVietorisPushforwardπNatTransV {U V X : AlgebraicSpace S} (j : U ⟶ X)
    [Etale j] (f : V ⟶ X) [Etale f] :
    restrictFunctor f ⋙ pushforward f ⟶
      restrictFunctor (fiberHom j f) ⋙ pushforward (fiberHom j f) where
  app F := mayerVietorisPushforwardπV j f F
  naturality := fun _ _ _ ↦ sorry

/-- Homotopy-to-derived unit of the underived composite `g_* ((-)|_W)`. -/
def mayerVietorisPushforwardCompositeUnit {W X : AlgebraicSpace S} (g : W ⟶ X)
    [Etale g] [(restrictFunctor g).Additive]
    [PreservesFiniteLimits (restrictFunctor g)]
    [PreservesFiniteColimits (restrictFunctor g)] :
    modulesMapHomotopy (restrictFunctor g) ⋙ modulesHomotopyToDerived (pushforward g) ⟶
      modulesQh X ⋙ modulesHomotopyFunctor (restrictFunctor g ⋙ pushforward g) :=
  (associator
      (modulesMapHomotopy (restrictFunctor g))
      (modulesMapHomotopy (pushforward g))
      (modulesQh X)).hom ≫
    (isoWhiskerRight
        (mapHomotopyCategoryCompIso (Iso.refl (restrictFunctor g ⋙ pushforward g)) (up ℤ))
        (modulesQh X)).hom ≫
      modulesHomotopyUnit (restrictFunctor g ⋙ pushforward g)

/-- The K-injective derived functor of `g_* ((-)|_W)` is a right-derived model of that
composite. -/
instance mayerVietorisPushforwardComposite_isRightDerived {W X : AlgebraicSpace S}
    (g : W ⟶ X) [Etale g] [(restrictFunctor g).Additive]
    [PreservesFiniteLimits (restrictFunctor g)]
    [PreservesFiniteColimits (restrictFunctor g)] :
    (modulesHomotopyFunctor (restrictFunctor g ⋙ pushforward g)).IsRightDerivedFunctor
      (mayerVietorisPushforwardCompositeUnit g)
      (@HomotopyCategory.quasiIso X.Modules _ ℤ (up ℤ) X.modulesAbelian.toPreadditive
        inferInstance) :=
  sorry

/-- Right-derived composition comparison
`R(g_* ((-)|_W)) ⟶ (-)|_W ⋙ Rg_*`. -/
def mayerVietorisPushforwardDerivedComparison {W X : AlgebraicSpace S} (g : W ⟶ X)
    [Etale g] [(restrictFunctor g).Additive]
    [PreservesFiniteLimits (restrictFunctor g)]
    [PreservesFiniteColimits (restrictFunctor g)] :
    modulesHomotopyFunctor (restrictFunctor g ⋙ pushforward g) ⟶
      restrictFunctorDerived g ⋙ pushforwardDerived g :=
  @RightDerived.Composition.comparisonOfModels
    (modulesHomotopy X) (modulesHomotopy W) (ModuleDerived X)
    (ModuleDerived X) (ModuleDerived W)
    inferInstance inferInstance inferInstance inferInstance inferInstance
    (modulesMapHomotopy (restrictFunctor g))
    (modulesHomotopyToDerived (pushforward g))
    (modulesQh X) (modulesQh W)
    (restrictFunctorDerived g) (pushforwardDerived g)
    (modulesHomotopyFunctor (restrictFunctor g ⋙ pushforward g))
    (@HomotopyCategory.quasiIso X.Modules _ ℤ (up ℤ) X.modulesAbelian.toPreadditive
      inferInstance)
    (modulesRestrictFactorshInv g)
    (modulesHomotopyUnit (pushforward g))
    (mayerVietorisPushforwardCompositeUnit g)
    inferInstance inferInstance

/-- The composition comparison `R(g_* g^*) ⟶ g^* ⋙ Rg_*` is an isomorphism. -/
instance isIso_mayerVietorisPushforwardDerivedComparison {W X : AlgebraicSpace S}
    (g : W ⟶ X) [Etale g] [(restrictFunctor g).Additive]
    [PreservesFiniteLimits (restrictFunctor g)]
    [PreservesFiniteColimits (restrictFunctor g)] :
    IsIso (mayerVietorisPushforwardDerivedComparison g) :=
  sorry

/-- Identification `R(g_* ((-)|_W)) ≅ (-)|_W ⋙ Rg_*` of derived functors on `D(𝒪_X)`. -/
def mayerVietorisPushforwardDerivedIso {W X : AlgebraicSpace S} (g : W ⟶ X)
    [Etale g] [(restrictFunctor g).Additive]
    [PreservesFiniteLimits (restrictFunctor g)]
    [PreservesFiniteColimits (restrictFunctor g)] :
    modulesHomotopyFunctor (restrictFunctor g ⋙ pushforward g) ≅
      restrictFunctorDerived g ⋙ pushforwardDerived g :=
  asIso (mayerVietorisPushforwardDerivedComparison g)

/-- The K-injective total right-derived functor of the identity on `𝒪_X`-modules is the
identity of `D(𝒪_X)`. -/
def mayerVietorisPushforwardDerivedIdIso (X : AlgebraicSpace S) :
    Functor.RightDerived.Homotopy.functor (𝟭 X.Modules) ≅ 𝟭 (ModuleDerived X) :=
  (Functor.RightDerived.Exact.homotopyIso (𝟭 X.Modules)).symm ≪≫
    ExactFunctor.MapDerivedCategory.idFunctorIso X.Modules

/-- On a K-injective complex, the cochain-level unit of `g_* ((-)|_W)` is an isomorphism. -/
theorem isIso_mayerVietorisPushforward_composite_unit_app {W X : AlgebraicSpace S}
    (g : W ⟶ X) [Etale g] [(restrictFunctor g).Additive] [(restrictFunctor g ⋙ pushforward g).Additive]
    (K : CochainComplex X.Modules ℤ) [K.IsKInjective] :
    IsIso ((Functor.RightDerived.KInjective.unit.{u}
        (restrictFunctor g ⋙ pushforward g)).app K) :=
  sorry

/-- After restriction of a K-injective termwise-injective complex, the K-injective unit of
`g_*` is an isomorphism, so `g_*` computes `Rg_*` on the restricted complex. -/
theorem isIso_mayerVietorisPushforward_unit_app_of_isKInjective {W X : AlgebraicSpace S}
    (g : W ⟶ X) [Etale g] [(restrictFunctor g).Additive]
    (K : CochainComplex X.Modules ℤ) [K.IsKInjective]
    [∀ n, Injective (K.X n)] :
    IsIso ((Functor.RightDerived.KInjective.unit.{u} (pushforward g)).app
      (((restrictFunctor g).mapHomologicalComplex (up ℤ)).obj K)) :=
  sorry

variable {U V X : AlgebraicSpace S} (j : U ⟶ X) [Etale j] (f : V ⟶ X) [Etale f]
variable [(restrictFunctor (fiberHom j f)).Additive]
variable [(restrictFunctor j).Additive]
variable [(restrictFunctor f).Additive]
variable [PreservesFiniteLimits (restrictFunctor (fiberHom j f))]
variable [PreservesFiniteColimits (restrictFunctor (fiberHom j f))]
variable [PreservesFiniteLimits (restrictFunctor j)]
variable [PreservesFiniteColimits (restrictFunctor j)]
variable [PreservesFiniteLimits (restrictFunctor f)]
variable [PreservesFiniteColimits (restrictFunctor f)]

/-- The cochain-level first Mayer–Vietoris arrow. -/
def mayerVietorisPushforwardCochainι (K : CochainComplex X.Modules ℤ) :
    K ⟶
      biprod (((restrictFunctor j ⋙ pushforward j).mapHomologicalComplex (up ℤ)).obj K)
        (((restrictFunctor f ⋙ pushforward f).mapHomologicalComplex (up ℤ)).obj K) :=
  biprod.lift
    ((Functor.mapHomologicalComplexIdIso X.Modules (up ℤ)).inv.app K ≫
      (NatTrans.mapHomologicalComplex (mayerVietorisPushforwardιNatTransU j) (up ℤ)).app K)
    ((Functor.mapHomologicalComplexIdIso X.Modules (up ℤ)).inv.app K ≫
      (NatTrans.mapHomologicalComplex (mayerVietorisPushforwardιNatTransV f) (up ℤ)).app K)

/-- The cochain-level second Mayer–Vietoris arrow. -/
def mayerVietorisPushforwardCochainπ (K : CochainComplex X.Modules ℤ) :
    biprod (((restrictFunctor j ⋙ pushforward j).mapHomologicalComplex (up ℤ)).obj K)
        (((restrictFunctor f ⋙ pushforward f).mapHomologicalComplex (up ℤ)).obj K) ⟶
      ((restrictFunctor (fiberHom j f) ⋙ pushforward (fiberHom j f)).mapHomologicalComplex
        (up ℤ)).obj K :=
  biprod.desc
    ((NatTrans.mapHomologicalComplex (mayerVietorisPushforwardπNatTransU j f) (up ℤ)).app K)
    (-(NatTrans.mapHomologicalComplex (mayerVietorisPushforwardπNatTransV j f) (up ℤ)).app K)

/-- The short complex of cochain complexes obtained by applying the module-level
Mayer–Vietoris arrows degreewise. -/
def mayerVietorisPushforwardCochainShortComplex (K : CochainComplex X.Modules ℤ) :
    ShortComplex (CochainComplex X.Modules ℤ) :=
  ShortComplex.mk (mayerVietorisPushforwardCochainι j f K)
    (mayerVietorisPushforwardCochainπ j f K) sorry

/-- Derived `U`-leg unit in `D(𝒪_X)`. -/
def mayerVietorisPushforwardιDerivedU (E : ModuleDerived X) :
    E ⟶ (pushforwardDerived j).obj ((restrictFunctorDerived j).obj E) :=
  (mayerVietorisPushforwardDerivedIdIso X).inv.app E ≫
    (Functor.RightDerived.Homotopy.mapNatTrans
      (mayerVietorisPushforwardιNatTransU j)).app E ≫
    (mayerVietorisPushforwardDerivedIso j).hom.app E

/-- Derived `V`-leg unit in `D(𝒪_X)`. -/
def mayerVietorisPushforwardιDerivedV (E : ModuleDerived X) :
    E ⟶ (pushforwardDerived f).obj ((restrictFunctorDerived f).obj E) :=
  (mayerVietorisPushforwardDerivedIdIso X).inv.app E ≫
    (Functor.RightDerived.Homotopy.mapNatTrans
      (mayerVietorisPushforwardιNatTransV f)).app E ≫
    (mayerVietorisPushforwardDerivedIso f).hom.app E

/-- Derived first Mayer–Vietoris arrow in `D(𝒪_X)`. -/
def mayerVietorisPushforwardιDerived (E : ModuleDerived X) :
    E ⟶
      biprod ((pushforwardDerived j).obj ((restrictFunctorDerived j).obj E))
        ((pushforwardDerived f).obj ((restrictFunctorDerived f).obj E)) :=
  biprod.lift (mayerVietorisPushforwardιDerivedU j E)
    (mayerVietorisPushforwardιDerivedV f E)

/-- Derived `U`-leg overlap restriction in `D(𝒪_X)`. -/
def mayerVietorisPushforwardπDerivedU (E : ModuleDerived X) :
    (pushforwardDerived j).obj ((restrictFunctorDerived j).obj E) ⟶
      (pushforwardDerived (fiberHom j f)).obj
        ((restrictFunctorDerived (fiberHom j f)).obj E) :=
  (mayerVietorisPushforwardDerivedIso j).inv.app E ≫
    (Functor.RightDerived.Homotopy.mapNatTrans
      (mayerVietorisPushforwardπNatTransU j f)).app E ≫
    (mayerVietorisPushforwardDerivedIso (fiberHom j f)).hom.app E

/-- Derived `V`-leg overlap restriction in `D(𝒪_X)`. -/
def mayerVietorisPushforwardπDerivedV (E : ModuleDerived X) :
    (pushforwardDerived f).obj ((restrictFunctorDerived f).obj E) ⟶
      (pushforwardDerived (fiberHom j f)).obj
        ((restrictFunctorDerived (fiberHom j f)).obj E) :=
  (mayerVietorisPushforwardDerivedIso f).inv.app E ≫
    (Functor.RightDerived.Homotopy.mapNatTrans
      (mayerVietorisPushforwardπNatTransV j f)).app E ≫
    (mayerVietorisPushforwardDerivedIso (fiberHom j f)).hom.app E

/-- Derived second Mayer–Vietoris arrow in `D(𝒪_X)`. -/
def mayerVietorisPushforwardπDerived (E : ModuleDerived X) :
    biprod ((pushforwardDerived j).obj ((restrictFunctorDerived j).obj E))
        ((pushforwardDerived f).obj ((restrictFunctorDerived f).obj E)) ⟶
      (pushforwardDerived (fiberHom j f)).obj
        ((restrictFunctorDerived (fiberHom j f)).obj E) :=
  biprod.desc (mayerVietorisPushforwardπDerivedU j f E)
    (-mayerVietorisPushforwardπDerivedV j f E)

variable [IsElementaryDistinguishedSquare j f]

/-- The cochain-level Mayer–Vietoris sequence is short exact. -/
theorem mayerVietorisPushforwardCochain_shortExact (K : CochainComplex X.Modules ℤ) :
    (mayerVietorisPushforwardCochainShortComplex j f K).ShortExact :=
  sorry

/-- Cochain-level connecting maps of the Mayer–Vietoris short exact sequences, as a natural
transformation `g_* ((-)|_W) ⋙ Q ⟶ Q ⋙ ((-)⟦1⟧)` along the overlap morphism. -/
def mayerVietorisPushforwardδCochain :
    (restrictFunctor (fiberHom j f) ⋙ pushforward (fiberHom j f)).mapHomologicalComplex (up ℤ) ⋙
        (DerivedCategory.Q : CochainComplex X.Modules ℤ ⥤ ModuleDerived X) ⟶
      (DerivedCategory.Q : CochainComplex X.Modules ℤ ⥤ ModuleDerived X) ⋙
        shiftFunctor (ModuleDerived X) (1 : ℤ) where
  app K := DerivedCategory.triangleOfSESδ (mayerVietorisPushforwardCochain_shortExact j f K)
  naturality := fun _ _ _ ↦ sorry

/-- The K-injective derived functor of the overlap composite is a cochain-level right-derived
model. -/
instance mayerVietorisPushforward_overlapComposite_isRightDerived :
    (Functor.RightDerived.KInjective.functor.{u}
        (restrictFunctor (fiberHom j f) ⋙ pushforward (fiberHom j f))).IsRightDerivedFunctor
      (Functor.RightDerived.KInjective.unit.{u}
        (restrictFunctor (fiberHom j f) ⋙ pushforward (fiberHom j f)))
      (HomologicalComplex.quasiIso X.Modules (up ℤ)) :=
  sorry

/-- Connecting morphism of derived functors, obtained by descending the cochain-level
`triangleOfSESδ` along the K-injective unit of the overlap composite. -/
def mayerVietorisPushforwardδNatTrans :
    Functor.RightDerived.Homotopy.functor
        (restrictFunctor (fiberHom j f) ⋙ pushforward (fiberHom j f)) ⟶
      shiftFunctor (ModuleDerived X) (1 : ℤ) :=
  (Functor.RightDerived.KInjective.functor.{u}
      (restrictFunctor (fiberHom j f) ⋙ pushforward (fiberHom j f))).rightDerivedDesc
    (Functor.RightDerived.KInjective.unit.{u}
      (restrictFunctor (fiberHom j f) ⋙ pushforward (fiberHom j f)))
    (HomologicalComplex.quasiIso X.Modules (up ℤ))
    (shiftFunctor (ModuleDerived X) (1 : ℤ))
    (mayerVietorisPushforwardδCochain j f)

/-- The connecting morphism of the Mayer–Vietoris triangle in `D(𝒪_X)`. -/
def mayerVietorisPushforwardδ (E : ModuleDerived X) :
    (pushforwardDerived (fiberHom j f)).obj
      ((restrictFunctorDerived (fiberHom j f)).obj E) ⟶ E⟦(1 : ℤ)⟧ :=
  (mayerVietorisPushforwardDerivedIso (fiberHom j f)).inv.app E ≫
    (mayerVietorisPushforwardδNatTrans j f).app E

/-- The Mayer–Vietoris distinguished-triangle data of étale pushforward in `D(𝒪_X)`. -/
def mayerVietorisPushforwardTriangle (E : ModuleDerived X) :
    Triangle (ModuleDerived X) :=
  Triangle.mk (mayerVietorisPushforwardιDerived j f E)
    (mayerVietorisPushforwardπDerived j f E) (mayerVietorisPushforwardδ j f E)

/-- The first vertex of the Mayer–Vietoris triangle is `E`. -/
theorem mayerVietorisPushforwardTriangle_obj₁ (E : ModuleDerived X) :
    (mayerVietorisPushforwardTriangle j f E).obj₁ = E :=
  sorry

/-- The second vertex of the Mayer–Vietoris triangle is
`Rj_{U,*} (E|_U) ⊞ Rj_{V,*} (E|_V)`. -/
theorem mayerVietorisPushforwardTriangle_obj₂ (E : ModuleDerived X) :
    (mayerVietorisPushforwardTriangle j f E).obj₂ =
      biprod ((pushforwardDerived j).obj ((restrictFunctorDerived j).obj E))
        ((pushforwardDerived f).obj ((restrictFunctorDerived f).obj E)) :=
  sorry

/-- The third vertex of the Mayer–Vietoris triangle is
`Rj_{U×_X V,*} (E|_{U×_X V})`. -/
theorem mayerVietorisPushforwardTriangle_obj₃ (E : ModuleDerived X) :
    (mayerVietorisPushforwardTriangle j f E).obj₃ =
      (pushforwardDerived (fiberHom j f)).obj
        ((restrictFunctorDerived (fiberHom j f)).obj E) :=
  sorry

/-- On `Q.obj K` for a K-injective termwise-injective complex `K`, the Mayer–Vietoris
triangle is isomorphic to `triangleOfSES` of the degreewise cochain short exact sequence. -/
def mayerVietorisPushforwardTriangle_eq_triangleOfSES
    (K : CochainComplex X.Modules ℤ) [K.IsKInjective] [∀ n, Injective (K.X n)]
    (h : (mayerVietorisPushforwardCochainShortComplex j f K).ShortExact) :
    mayerVietorisPushforwardTriangle j f (DerivedCategory.Q.obj K) ≅
      DerivedCategory.triangleOfSES h :=
  let T := mayerVietorisPushforwardTriangle j f (DerivedCategory.Q.obj K)
  let T' := DerivedCategory.triangleOfSES h
  let eW :=
    (mayerVietorisPushforwardDerivedIso (fiberHom j f)).symm.app (DerivedCategory.Q.obj K) ≪≫
      (@asIso _ _ _ _
        ((Functor.RightDerived.KInjective.unit.{u}
            (restrictFunctor (fiberHom j f) ⋙ pushforward (fiberHom j f))).app K)
        (isIso_mayerVietorisPushforward_composite_unit_app (fiberHom j f) K)).symm
  let eU :=
    (mayerVietorisPushforwardDerivedIso j).symm.app (DerivedCategory.Q.obj K) ≪≫
      (@asIso _ _ _ _
        ((Functor.RightDerived.KInjective.unit.{u}
            (restrictFunctor j ⋙ pushforward j)).app K)
        (isIso_mayerVietorisPushforward_composite_unit_app j K)).symm
  let eV :=
    (mayerVietorisPushforwardDerivedIso f).symm.app (DerivedCategory.Q.obj K) ≪≫
      (@asIso _ _ _ _
        ((Functor.RightDerived.KInjective.unit.{u}
            (restrictFunctor f ⋙ pushforward f)).app K)
        (isIso_mayerVietorisPushforward_composite_unit_app f K)).symm
  let KU := ((restrictFunctor j ⋙ pushforward j).mapHomologicalComplex (up ℤ)).obj K
  let KV := ((restrictFunctor f ⋙ pushforward f).mapHomologicalComplex (up ℤ)).obj K
  let e₁ : T.obj₁ ≅ T'.obj₁ := Iso.refl _
  let e₂ : T.obj₂ ≅ T'.obj₂ :=
    Iso.mk
      (biprod.desc (eU.hom ≫ DerivedCategory.Q.map (biprod.inl : KU ⟶ KU ⊞ KV))
        (eV.hom ≫ DerivedCategory.Q.map (biprod.inr : KV ⟶ KU ⊞ KV)))
      (biprod.lift (DerivedCategory.Q.map (biprod.fst : KU ⊞ KV ⟶ KU) ≫ eU.inv)
        (DerivedCategory.Q.map (biprod.snd : KU ⊞ KV ⟶ KV) ≫ eV.inv))
      sorry sorry
  Iso.mk (Triangle.homMk T T' e₁.hom e₂.hom eW.hom sorry sorry sorry)
    (Triangle.homMk T' T e₁.inv e₂.inv eW.inv sorry sorry sorry) sorry sorry

/-- The first component of the `triangleOfSES` comparison is the identity on
`Q.obj K`. -/
theorem mayerVietorisPushforwardTriangle_eq_triangleOfSES_hom₁
    (K : CochainComplex X.Modules ℤ) [K.IsKInjective] [∀ n, Injective (K.X n)]
    (h : (mayerVietorisPushforwardCochainShortComplex j f K).ShortExact) :
    (mayerVietorisPushforwardTriangle_eq_triangleOfSES j f K h).hom.hom₁ =
      𝟙 _ :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules
