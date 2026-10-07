module

public import Mathlib.Algebra.Homology.Additive
public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Exact
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Exact.Composition
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Exact.Identity
public import stacks_project.Chap65.Lemma_65_7_3_Pullback
public import stacks_project.Chap66.Lemma_66_16_5_Pullback
public import stacks_project.Chap66.Lemma_66_20_1_Sheaf
public import stacks_project.Chap66.Lemma_66_26_3_Glueing
public import stacks_project.Chap75.Definition_75_9_1_Square
public import stacks_project.Chap75.Lemma_75_10_6_LowerShriek
public import stacks_project.Chap75.Lemma_75_3_1_Restrict

/-!
# Mayer–Vietoris comparison maps for étale lower shriek

An elementary distinguished square `(j : U ⟶ X, f : V ⟶ X)` determines comparison
maps of étale extension by zero of an `𝒪_X`-module along the three legs, assembled
into a short complex and into a triangle in `D(𝒪_X)`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules CategoryTheory.Limits
open CategoryTheory.Pretriangulated ComplexShape
open AlgebraicGeometry.AlgebraicSpace.SmallEtaleModuleGlueing (restrictFunctorComp)

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

variable {S : Scheme.{u}}

/-- The structure morphism `U ×_X V ⟶ X`, as `Limits.pullback.fst j f ≫ j`. -/
abbrev fiberHom {U V X : AlgebraicSpace S} (j : U ⟶ X) (f : V ⟶ X) :
    Limits.pullback j f ⟶ X :=
  Limits.pullback.fst j f ≫ j

/-- The two structure maps of `U ×_X V` agree as morphisms to `X`. -/
def fiberHom_eq {U V X : AlgebraicSpace S} (j : U ⟶ X) (f : V ⟶ X) :
    fiberHom j f = Limits.pullback.snd j f ≫ f :=
  Limits.pullback.condition

/-- Transport `j_! F|_U` along an equality of étale morphisms to `X`. -/
def lowerShriekRestrictObj_eq {W X : AlgebraicSpace S} {p q : W ⟶ X}
    [hp : Etale p] [hq : Etale q] (h : p = q) (F : X.Modules) :
    (lowerShriek p).obj (restrict F p) = (lowerShriek q).obj (restrict F q) :=
  Eq.rec (motive := fun r (_ : p = r) =>
      ∀ hr : Etale r,
        (@lowerShriek S W X p hp).obj (@restrict S W X F p hp) =
          (@lowerShriek S W X r hr).obj (@restrict S W X F r hr))
    (fun hr =>
      congrArg (fun inst : Etale p =>
          (@lowerShriek S W X p inst).obj (@restrict S W X F p inst))
        (Subsingleton.elim hp hr))
    h hq

/-- The comparison `j_{W!} F|_W ⟶ j_{U!} F|_U` of étale lower shriek along a
factorization `W ⟶ U ⟶ X`. -/
def lowerShriekRestrictHom {W U X : AlgebraicSpace S} (p : W ⟶ U) [Etale p]
    (j : U ⟶ X) [Etale j] (F : X.Modules) :
    (lowerShriek (p ≫ j)).obj (restrict F (p ≫ j)) ⟶
      (lowerShriek j).obj (restrict F j) :=
  ((lowerShriekAdjunction (p ≫ j)).homEquiv (restrict F (p ≫ j))
      ((lowerShriek j).obj (restrict F j))).symm
    ((restrictFunctorComp p j).inv.app F ≫
      (restrictFunctor p).map ((lowerShriekAdjunction j).unit.app (restrict F j)) ≫
      (restrictFunctorComp p j).hom.app ((lowerShriek j).obj (restrict F j)))

/-- `lowerShriekRestrictHom` is the adjunct of the restricted unit of
`lowerShriekAdjunction j`, after identifying successive restrictions with
restriction along the composite. -/
theorem lowerShriekRestrictHom_eq {W U X : AlgebraicSpace S} (p : W ⟶ U) [Etale p]
    (j : U ⟶ X) [Etale j] (F : X.Modules) :
    lowerShriekRestrictHom p j F =
      ((lowerShriekAdjunction (p ≫ j)).homEquiv (restrict F (p ≫ j))
          ((lowerShriek j).obj (restrict F j))).symm
        ((restrictFunctorComp p j).inv.app F ≫
          (restrictFunctor p).map ((lowerShriekAdjunction j).unit.app (restrict F j)) ≫
          (restrictFunctorComp p j).hom.app ((lowerShriek j).obj (restrict F j))) :=
  sorry

/-- The `U`-leg of the Mayer–Vietoris lower-shriek comparison. -/
def mayerVietorisLowerShriekιU {U V X : AlgebraicSpace S} (j : U ⟶ X) [Etale j]
    (f : V ⟶ X) [Etale f] (F : X.Modules) :
    (lowerShriek (fiberHom j f)).obj (restrict F (fiberHom j f)) ⟶
      (lowerShriek j).obj (restrict F j) :=
  lowerShriekRestrictHom (Limits.pullback.fst j f) j F

/-- The `V`-leg of the Mayer–Vietoris lower-shriek comparison, transported along
`fiberHom_eq`. -/
def mayerVietorisLowerShriekιV {U V X : AlgebraicSpace S} (j : U ⟶ X) [Etale j]
    (f : V ⟶ X) [Etale f] (F : X.Modules) :
    (lowerShriek (fiberHom j f)).obj (restrict F (fiberHom j f)) ⟶
      (lowerShriek f).obj (restrict F f) :=
  eqToHom (lowerShriekRestrictObj_eq (fiberHom_eq j f) F) ≫
    lowerShriekRestrictHom (Limits.pullback.snd j f) f F

/-- The first Mayer–Vietoris arrow
`j_{U×_X V!} F|_{U×_X V} ⟶ j_{U!} F|_U ⊞ j_{V!} F|_V`, with a sign on the `V`-leg. -/
def mayerVietorisLowerShriekι {U V X : AlgebraicSpace S} (j : U ⟶ X) [Etale j]
    (f : V ⟶ X) [Etale f] (F : X.Modules) :
    (lowerShriek (fiberHom j f)).obj (restrict F (fiberHom j f)) ⟶
      biprod ((lowerShriek j).obj (restrict F j)) ((lowerShriek f).obj (restrict F f)) :=
  biprod.lift (mayerVietorisLowerShriekιU j f F) (-mayerVietorisLowerShriekιV j f F)

/-- The second Mayer–Vietoris arrow `j_{U!} F|_U ⊞ j_{V!} F|_V ⟶ F`, as the
biproduct of the two lower-shriek counits. -/
def mayerVietorisLowerShriekπ {U V X : AlgebraicSpace S} (j : U ⟶ X) [Etale j]
    (f : V ⟶ X) [Etale f] (F : X.Modules) :
    biprod ((lowerShriek j).obj (restrict F j)) ((lowerShriek f).obj (restrict F f)) ⟶ F :=
  biprod.desc ((lowerShriekAdjunction j).counit.app F)
    ((lowerShriekAdjunction f).counit.app F)

/-- The three-term complex of étale lower shriek along an elementary distinguished
square. -/
def mayerVietorisLowerShriekShortComplex {U V X : AlgebraicSpace S} (j : U ⟶ X)
    [Etale j] (f : V ⟶ X) [Etale f] (F : X.Modules) : ShortComplex X.Modules :=
  ShortComplex.mk (mayerVietorisLowerShriekι j f F) (mayerVietorisLowerShriekπ j f F) sorry

/-- The left vertex of the Mayer–Vietoris short complex is
`j_{U×_X V!} F|_{U×_X V}`. -/
theorem mayerVietorisLowerShriekShortComplex_X₁ {U V X : AlgebraicSpace S}
    (j : U ⟶ X) [Etale j] (f : V ⟶ X) [Etale f] (F : X.Modules) :
    (mayerVietorisLowerShriekShortComplex j f F).X₁ =
      (lowerShriek (fiberHom j f)).obj (restrict F (fiberHom j f)) :=
  sorry

/-- The first arrow of the Mayer–Vietoris short complex is
`mayerVietorisLowerShriekι`. -/
theorem mayerVietorisLowerShriekShortComplex_f {U V X : AlgebraicSpace S}
    (j : U ⟶ X) [Etale j] (f : V ⟶ X) [Etale f] (F : X.Modules) :
    (mayerVietorisLowerShriekShortComplex j f F).f = mayerVietorisLowerShriekι j f F :=
  sorry

/-- The second arrow of the Mayer–Vietoris short complex is
`mayerVietorisLowerShriekπ`. -/
theorem mayerVietorisLowerShriekShortComplex_g {U V X : AlgebraicSpace S}
    (j : U ⟶ X) [Etale j] (f : V ⟶ X) [Etale f] (F : X.Modules) :
    (mayerVietorisLowerShriekShortComplex j f F).g = mayerVietorisLowerShriekπ j f F :=
  sorry

/-- The `U`-leg comparison as a natural transformation of étale extension-by-zero
functors on `X`. -/
def mayerVietorisLowerShriekιNatTransU {U V X : AlgebraicSpace S} (j : U ⟶ X)
    [Etale j] (f : V ⟶ X) [Etale f] :
    restrictFunctor (fiberHom j f) ⋙ lowerShriek (fiberHom j f) ⟶
      restrictFunctor j ⋙ lowerShriek j where
  app F := mayerVietorisLowerShriekιU j f F
  naturality := fun _ _ _ ↦ sorry

/-- The `V`-leg comparison as a natural transformation of étale extension-by-zero
functors on `X`. -/
def mayerVietorisLowerShriekιNatTransV {U V X : AlgebraicSpace S} (j : U ⟶ X)
    [Etale j] (f : V ⟶ X) [Etale f] :
    restrictFunctor (fiberHom j f) ⋙ lowerShriek (fiberHom j f) ⟶
      restrictFunctor f ⋙ lowerShriek f where
  app F := mayerVietorisLowerShriekιV j f F
  naturality := fun _ _ _ ↦ sorry

/-- The `U`-leg counit as a natural transformation `j_! j^* ⟶ 𝟭`. -/
def mayerVietorisLowerShriekπNatTransU {U X : AlgebraicSpace S} (j : U ⟶ X)
    [Etale j] :
    restrictFunctor j ⋙ lowerShriek j ⟶ 𝟭 X.Modules :=
  (lowerShriekAdjunction j).counit

/-- The `V`-leg counit as a natural transformation `f_! f^* ⟶ 𝟭`. -/
def mayerVietorisLowerShriekπNatTransV {V X : AlgebraicSpace S} (f : V ⟶ X)
    [Etale f] :
    restrictFunctor f ⋙ lowerShriek f ⟶ 𝟭 X.Modules :=
  (lowerShriekAdjunction f).counit

variable {U V X : AlgebraicSpace S} (j : U ⟶ X) [Etale j] (f : V ⟶ X) [Etale f]
variable [(restrictFunctor (fiberHom j f)).Additive] [(lowerShriek (fiberHom j f)).Additive]
variable [(restrictFunctor j).Additive] [(lowerShriek j).Additive]
variable [(restrictFunctor f).Additive] [(lowerShriek f).Additive]
variable [(restrictFunctor (fiberHom j f) ⋙ lowerShriek (fiberHom j f)).Additive]
variable [(restrictFunctor j ⋙ lowerShriek j).Additive]
variable [(restrictFunctor f ⋙ lowerShriek f).Additive]
variable [PreservesFiniteLimits (restrictFunctor (fiberHom j f))]
variable [PreservesFiniteColimits (restrictFunctor (fiberHom j f))]
variable [PreservesFiniteLimits (lowerShriek (fiberHom j f))]
variable [PreservesFiniteColimits (lowerShriek (fiberHom j f))]
variable [PreservesFiniteLimits (restrictFunctor j)]
variable [PreservesFiniteColimits (restrictFunctor j)]
variable [PreservesFiniteLimits (lowerShriek j)]
variable [PreservesFiniteColimits (lowerShriek j)]
variable [PreservesFiniteLimits (restrictFunctor f)]
variable [PreservesFiniteColimits (restrictFunctor f)]
variable [PreservesFiniteLimits (lowerShriek f)]
variable [PreservesFiniteColimits (lowerShriek f)]

/-- Identification of the derived functor of restriction followed by lower shriek
with the composite of `restrictFunctorDerived` and `lowerShriekDerived`. -/
def mayerVietorisLowerShriekDerivedCompIso {W : AlgebraicSpace S} (g : W ⟶ X)
    [Etale g]
    [(restrictFunctor g).Additive] [(lowerShriek g).Additive]
    [PreservesFiniteLimits (restrictFunctor g)]
    [PreservesFiniteColimits (restrictFunctor g)]
    [PreservesFiniteLimits (lowerShriek g)]
    [PreservesFiniteColimits (lowerShriek g)] :
    ((ExactFunctor.of (restrictFunctor g)).comp
        (ExactFunctor.of (lowerShriek g))).mapDerivedCategory ≅
      restrictFunctorDerived g ⋙ lowerShriekDerived g :=
  ExactFunctor.MapDerivedCategory.compFunctorIso (ExactFunctor.of (restrictFunctor g))
    (ExactFunctor.of (lowerShriek g))

/-- Bundled exact-functor form of the `U`-leg comparison. -/
def mayerVietorisLowerShriekιExactU :
    ExactFunctor.of (restrictFunctor (fiberHom j f) ⋙ lowerShriek (fiberHom j f)) ⟶
      ExactFunctor.of (restrictFunctor j ⋙ lowerShriek j) where
  hom := mayerVietorisLowerShriekιNatTransU j f

/-- Bundled exact-functor form of the `V`-leg comparison. -/
def mayerVietorisLowerShriekιExactV :
    ExactFunctor.of (restrictFunctor (fiberHom j f) ⋙ lowerShriek (fiberHom j f)) ⟶
      ExactFunctor.of (restrictFunctor f ⋙ lowerShriek f) where
  hom := mayerVietorisLowerShriekιNatTransV j f

/-- Bundled exact-functor form of the `U`-leg counit. -/
def mayerVietorisLowerShriekπExactU :
    ExactFunctor.of (restrictFunctor j ⋙ lowerShriek j) ⟶ ExactFunctor.id X.Modules where
  hom := mayerVietorisLowerShriekπNatTransU j

/-- Bundled exact-functor form of the `V`-leg counit. -/
def mayerVietorisLowerShriekπExactV :
    ExactFunctor.of (restrictFunctor f ⋙ lowerShriek f) ⟶ ExactFunctor.id X.Modules where
  hom := mayerVietorisLowerShriekπNatTransV f

/-- Canonical iso from `mapDerivedCategory` of the composite functor to the
composite of the derived functors, specialized to a morphism `g`. -/
def mayerVietorisLowerShriekOfCompIso {W : AlgebraicSpace S} (g : W ⟶ X)
    [Etale g]
    [(restrictFunctor g).Additive] [(lowerShriek g).Additive]
    [PreservesFiniteLimits (restrictFunctor g)]
    [PreservesFiniteColimits (restrictFunctor g)]
    [PreservesFiniteLimits (lowerShriek g)]
    [PreservesFiniteColimits (lowerShriek g)] :
    (ExactFunctor.of (restrictFunctor g ⋙ lowerShriek g)).mapDerivedCategory ≅
      restrictFunctorDerived g ⋙ lowerShriekDerived g :=
  ExactFunctor.MapDerivedCategory.mapIso
      ((exactFunctor X.Modules X.Modules).isoMk (Iso.refl _)) ≪≫
    mayerVietorisLowerShriekDerivedCompIso g

/-- Derived `U`-leg comparison in `D(𝒪_X)`. -/
def mayerVietorisLowerShriekιDerivedU (E : ModuleDerived X) :
    (lowerShriekDerived (fiberHom j f)).obj
        ((restrictFunctorDerived (fiberHom j f)).obj E) ⟶
      (lowerShriekDerived j).obj ((restrictFunctorDerived j).obj E) :=
  (mayerVietorisLowerShriekOfCompIso (fiberHom j f)).inv.app E ≫
    (ExactFunctor.MapDerivedCategory.map (mayerVietorisLowerShriekιExactU j f)).app E ≫
    (mayerVietorisLowerShriekOfCompIso j).hom.app E

/-- Derived `V`-leg comparison in `D(𝒪_X)`. -/
def mayerVietorisLowerShriekιDerivedV (E : ModuleDerived X) :
    (lowerShriekDerived (fiberHom j f)).obj
        ((restrictFunctorDerived (fiberHom j f)).obj E) ⟶
      (lowerShriekDerived f).obj ((restrictFunctorDerived f).obj E) :=
  (mayerVietorisLowerShriekOfCompIso (fiberHom j f)).inv.app E ≫
    (ExactFunctor.MapDerivedCategory.map (mayerVietorisLowerShriekιExactV j f)).app E ≫
    (mayerVietorisLowerShriekOfCompIso f).hom.app E

/-- Derived first Mayer–Vietoris arrow in `D(𝒪_X)`. -/
def mayerVietorisLowerShriekιDerived (E : ModuleDerived X) :
    (lowerShriekDerived (fiberHom j f)).obj
        ((restrictFunctorDerived (fiberHom j f)).obj E) ⟶
      biprod ((lowerShriekDerived j).obj ((restrictFunctorDerived j).obj E))
        ((lowerShriekDerived f).obj ((restrictFunctorDerived f).obj E)) :=
  biprod.lift (mayerVietorisLowerShriekιDerivedU j f E)
    (-mayerVietorisLowerShriekιDerivedV j f E)

/-- Derived `U`-leg counit in `D(𝒪_X)`. -/
def mayerVietorisLowerShriekπDerivedU (E : ModuleDerived X) :
    (lowerShriekDerived j).obj ((restrictFunctorDerived j).obj E) ⟶ E :=
  (mayerVietorisLowerShriekOfCompIso j).inv.app E ≫
    (ExactFunctor.MapDerivedCategory.map (mayerVietorisLowerShriekπExactU j)).app E ≫
    (ExactFunctor.MapDerivedCategory.idObjIso X.Modules E).hom

/-- Derived `V`-leg counit in `D(𝒪_X)`. -/
def mayerVietorisLowerShriekπDerivedV (E : ModuleDerived X) :
    (lowerShriekDerived f).obj ((restrictFunctorDerived f).obj E) ⟶ E :=
  (mayerVietorisLowerShriekOfCompIso f).inv.app E ≫
    (ExactFunctor.MapDerivedCategory.map (mayerVietorisLowerShriekπExactV f)).app E ≫
    (ExactFunctor.MapDerivedCategory.idObjIso X.Modules E).hom

/-- Derived second Mayer–Vietoris arrow in `D(𝒪_X)`. -/
def mayerVietorisLowerShriekπDerived (E : ModuleDerived X) :
    biprod ((lowerShriekDerived j).obj ((restrictFunctorDerived j).obj E))
        ((lowerShriekDerived f).obj ((restrictFunctorDerived f).obj E)) ⟶ E :=
  biprod.desc (mayerVietorisLowerShriekπDerivedU j E)
    (mayerVietorisLowerShriekπDerivedV f E)

/-- Identity comparison for cochain complexes of `𝒪_X`-modules. -/
def modulesMapHomologicalComplexIdIso :
    (𝟭 X.Modules).mapHomologicalComplex (up ℤ) ≅ 𝟭 (CochainComplex X.Modules ℤ) :=
  Functor.mapHomologicalComplexIdIso X.Modules (up ℤ)

/-- The cochain-level first Mayer–Vietoris arrow. -/
def mayerVietorisLowerShriekCochainι (K : CochainComplex X.Modules ℤ) :
    ((restrictFunctor (fiberHom j f) ⋙ lowerShriek (fiberHom j f)).mapHomologicalComplex
        (up ℤ)).obj K ⟶
      biprod (((restrictFunctor j ⋙ lowerShriek j).mapHomologicalComplex (up ℤ)).obj K)
        (((restrictFunctor f ⋙ lowerShriek f).mapHomologicalComplex (up ℤ)).obj K) :=
  biprod.lift
    ((NatTrans.mapHomologicalComplex (mayerVietorisLowerShriekιNatTransU j f)
        (up ℤ)).app K)
    (-(NatTrans.mapHomologicalComplex (mayerVietorisLowerShriekιNatTransV j f)
        (up ℤ)).app K)

/-- The cochain-level second Mayer–Vietoris arrow. -/
def mayerVietorisLowerShriekCochainπ (K : CochainComplex X.Modules ℤ) :
    biprod (((restrictFunctor j ⋙ lowerShriek j).mapHomologicalComplex (up ℤ)).obj K)
        (((restrictFunctor f ⋙ lowerShriek f).mapHomologicalComplex (up ℤ)).obj K) ⟶ K :=
  biprod.desc
    ((NatTrans.mapHomologicalComplex (mayerVietorisLowerShriekπNatTransU j) (up ℤ)).app K ≫
      modulesMapHomologicalComplexIdIso.hom.app K)
    ((NatTrans.mapHomologicalComplex (mayerVietorisLowerShriekπNatTransV f) (up ℤ)).app K ≫
      modulesMapHomologicalComplexIdIso.hom.app K)

/-- The short complex of cochain complexes obtained by applying the module-level
Mayer–Vietoris arrows degreewise. -/
def mayerVietorisLowerShriekCochainShortComplex (K : CochainComplex X.Modules ℤ) :
    ShortComplex (CochainComplex X.Modules ℤ) :=
  ShortComplex.mk (mayerVietorisLowerShriekCochainι j f K)
    (mayerVietorisLowerShriekCochainπ j f K) sorry

variable [IsElementaryDistinguishedSquare j f]

/-- The cochain-level Mayer–Vietoris sequence is short exact. -/
theorem mayerVietorisLowerShriekCochain_shortExact (K : CochainComplex X.Modules ℤ) :
    (mayerVietorisLowerShriekCochainShortComplex j f K).ShortExact :=
  sorry

/-- The connecting morphism of the Mayer–Vietoris triangle in `D(𝒪_X)`, obtained
from `triangleOfSESδ` of a cochain-level short exact sequence representing `E`. -/
def mayerVietorisLowerShriekδ (E : ModuleDerived X)
    (h : (mayerVietorisLowerShriekCochainShortComplex j f
            (DerivedCategory.Q.objPreimage E)).ShortExact) :
    E ⟶ ((lowerShriekDerived (fiberHom j f)).obj
      ((restrictFunctorDerived (fiberHom j f)).obj E))⟦(1 : ℤ)⟧ :=
  (DerivedCategory.Q.objObjPreimageIso E).inv ≫
    DerivedCategory.triangleOfSESδ h ≫
    ((restrictFunctor (fiberHom j f) ⋙ lowerShriek (fiberHom j f)).mapDerivedCategoryFactors.inv.app
        (DerivedCategory.Q.objPreimage E))⟦(1 : ℤ)⟧' ≫
    ((restrictFunctor (fiberHom j f) ⋙ lowerShriek (fiberHom j f)).mapDerivedCategory.map
        (DerivedCategory.Q.objObjPreimageIso E).hom)⟦(1 : ℤ)⟧' ≫
    (mayerVietorisLowerShriekOfCompIso (fiberHom j f)).hom.app E⟦(1 : ℤ)⟧'

/-- The Mayer–Vietoris distinguished-triangle data of étale lower shriek in
`D(𝒪_X)`. -/
def mayerVietorisLowerShriekTriangle (E : ModuleDerived X)
    (h : (mayerVietorisLowerShriekCochainShortComplex j f
            (DerivedCategory.Q.objPreimage E)).ShortExact) :
    Triangle (ModuleDerived X) :=
  Triangle.mk (mayerVietorisLowerShriekιDerived j f E)
    (mayerVietorisLowerShriekπDerived j f E) (mayerVietorisLowerShriekδ j f E h)

/-- The first vertex of the Mayer–Vietoris triangle is
`j_{U×_X V!} (E|_{U×_X V})`. -/
theorem mayerVietorisLowerShriekTriangle_obj₁ (E : ModuleDerived X)
    (h : (mayerVietorisLowerShriekCochainShortComplex j f
            (DerivedCategory.Q.objPreimage E)).ShortExact) :
    (mayerVietorisLowerShriekTriangle j f E h).obj₁ =
      (lowerShriekDerived (fiberHom j f)).obj
        ((restrictFunctorDerived (fiberHom j f)).obj E) :=
  sorry

/-- The second vertex of the Mayer–Vietoris triangle is
`j_{U!} (E|_U) ⊞ j_{V!} (E|_V)`. -/
theorem mayerVietorisLowerShriekTriangle_obj₂ (E : ModuleDerived X)
    (h : (mayerVietorisLowerShriekCochainShortComplex j f
            (DerivedCategory.Q.objPreimage E)).ShortExact) :
    (mayerVietorisLowerShriekTriangle j f E h).obj₂ =
      biprod ((lowerShriekDerived j).obj ((restrictFunctorDerived j).obj E))
        ((lowerShriekDerived f).obj ((restrictFunctorDerived f).obj E)) :=
  sorry

/-- The third vertex of the Mayer–Vietoris triangle is `E`. -/
theorem mayerVietorisLowerShriekTriangle_obj₃ (E : ModuleDerived X)
    (h : (mayerVietorisLowerShriekCochainShortComplex j f
            (DerivedCategory.Q.objPreimage E)).ShortExact) :
    (mayerVietorisLowerShriekTriangle j f E h).obj₃ = E :=
  sorry

/-- On `Q.obj K`, the Mayer–Vietoris triangle is isomorphic to `triangleOfSES` of
the degreewise cochain short exact sequence. -/
def mayerVietorisLowerShriekTriangle_eq_triangleOfSES
    (K : CochainComplex X.Modules ℤ)
    (h : (mayerVietorisLowerShriekCochainShortComplex j f K).ShortExact)
    (h' : (mayerVietorisLowerShriekCochainShortComplex j f
             (DerivedCategory.Q.objPreimage (DerivedCategory.Q.obj K))).ShortExact) :
    mayerVietorisLowerShriekTriangle j f (DerivedCategory.Q.obj K) h' ≅
      DerivedCategory.triangleOfSES h :=
  let T := mayerVietorisLowerShriekTriangle j f (DerivedCategory.Q.obj K) h'
  let T' := DerivedCategory.triangleOfSES h
  let KU := ((restrictFunctor j ⋙ lowerShriek j).mapHomologicalComplex (up ℤ)).obj K
  let KV := ((restrictFunctor f ⋙ lowerShriek f).mapHomologicalComplex (up ℤ)).obj K
  let eW :=
    (mayerVietorisLowerShriekOfCompIso (fiberHom j f)).symm.app (DerivedCategory.Q.obj K) ≪≫
      ((restrictFunctor (fiberHom j f) ⋙
          lowerShriek (fiberHom j f)).mapDerivedCategoryFactors.app K)
  let eU :=
    (mayerVietorisLowerShriekOfCompIso j).symm.app (DerivedCategory.Q.obj K) ≪≫
      ((restrictFunctor j ⋙ lowerShriek j).mapDerivedCategoryFactors.app K)
  let eV :=
    (mayerVietorisLowerShriekOfCompIso f).symm.app (DerivedCategory.Q.obj K) ≪≫
      ((restrictFunctor f ⋙ lowerShriek f).mapDerivedCategoryFactors.app K)
  let e₂ : T.obj₂ ≅ T'.obj₂ :=
    Iso.mk
      (biprod.desc (eU.hom ≫ DerivedCategory.Q.map (biprod.inl : KU ⟶ KU ⊞ KV))
        (eV.hom ≫ DerivedCategory.Q.map (biprod.inr : KV ⟶ KU ⊞ KV)))
      (biprod.lift (DerivedCategory.Q.map (biprod.fst : KU ⊞ KV ⟶ KU) ≫ eU.inv)
        (DerivedCategory.Q.map (biprod.snd : KU ⊞ KV ⟶ KV) ≫ eV.inv))
      sorry sorry
  Iso.mk (Triangle.homMk T T' eW.hom e₂.hom (𝟙 _) sorry sorry sorry)
    (Triangle.homMk T' T eW.inv e₂.inv (𝟙 _) sorry sorry sorry) sorry sorry

/-- The third component of the `triangleOfSES` comparison is the identity on
`Q.obj K`. -/
theorem mayerVietorisLowerShriekTriangle_eq_triangleOfSES_hom₃
    (K : CochainComplex X.Modules ℤ)
    (h : (mayerVietorisLowerShriekCochainShortComplex j f K).ShortExact)
    (h' : (mayerVietorisLowerShriekCochainShortComplex j f
             (DerivedCategory.Q.objPreimage (DerivedCategory.Q.obj K))).ShortExact) :
    (mayerVietorisLowerShriekTriangle_eq_triangleOfSES j f K h h').hom.hom₃ = 𝟙 _ :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules
