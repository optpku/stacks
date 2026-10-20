module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.LowerShriek.BaseChange
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Restriction
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Pullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Etale.BaseChange
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Exact.Square

/-! # Derived lower shriek and étale base change

Exact extension by zero induces a functor on unbounded derived module categories.
Its canonical base-change isomorphism commutes with étale restriction.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules CategoryTheory.Limits CategoryTheory.Functor

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

variable {S : Scheme.{u}} {U X : AlgebraicSpace S}

/-- The derived étale lower-shriek functor `j_! : D(𝒪_U) ⥤ D(𝒪_X)`. -/
def lowerShriekDerived (f : U ⟶ X) [Etale f]
    [Abelian U.Modules] [Abelian X.Modules]
    [(lowerShriek f).Additive]
    [PreservesFiniteLimits (lowerShriek f)]
    [PreservesFiniteColimits (lowerShriek f)] :
    ModuleDerived U ⥤ ModuleDerived X :=
  @Functor.mapDerivedCategory U.Modules _ U.modulesAbelian (modulesHasDerivedCategory U)
    X.Modules _ X.modulesAbelian (modulesHasDerivedCategory X) (lowerShriek f)
    inferInstance inferInstance inferInstance

/-- Derived étale lower shriek is `mapDerivedCategory` of underived étale lower shriek. -/
theorem lowerShriekDerived_eq (f : U ⟶ X) [Etale f]
    [Abelian U.Modules] [Abelian X.Modules]
    [(lowerShriek f).Additive]
    [PreservesFiniteLimits (lowerShriek f)]
    [PreservesFiniteColimits (lowerShriek f)] :
    lowerShriekDerived f =
      @Functor.mapDerivedCategory U.Modules _ U.modulesAbelian (modulesHasDerivedCategory U)
        X.Modules _ X.modulesAbelian (modulesHasDerivedCategory X) (lowerShriek f)
        inferInstance inferInstance inferInstance :=
  rfl

section BaseChange

variable {X' Y' Y : AlgebraicSpace S}
variable {h : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
variable [Etale f] [Etale f'] [Etale g] [Etale h]

variable [Abelian X.Modules] [Abelian X'.Modules] [Abelian Y.Modules] [Abelian Y'.Modules]
variable [(lowerShriek f).Additive] [(lowerShriek f').Additive]
variable [(restrictFunctor g).Additive] [(restrictFunctor h).Additive]
variable [PreservesFiniteLimits (lowerShriek f)]
variable [PreservesFiniteColimits (lowerShriek f)]
variable [PreservesFiniteLimits (lowerShriek f')]
variable [PreservesFiniteColimits (lowerShriek f')]
variable [PreservesFiniteLimits (restrictFunctor g)]
variable [PreservesFiniteColimits (restrictFunctor g)]
variable [PreservesFiniteLimits (restrictFunctor h)]
variable [PreservesFiniteColimits (restrictFunctor h)]

/-- The derived étale lower-shriek Beck--Chevalley isomorphism of functors on `D(𝒪_X)`. -/
def derivedLowerShriekEtaleBaseChangeNatIso (h_cart : IsPullback h f' f g) :
    lowerShriekDerived f ⋙ restrictFunctorDerived g ≅
      restrictFunctorDerived h ⋙ lowerShriekDerived f' :=
  @ExactFunctor.MapDerivedCategory.squareIso
    X.Modules Y.Modules X'.Modules Y'.Modules _ _ _ _
    X.modulesAbelian Y.modulesAbelian X'.modulesAbelian Y'.modulesAbelian
    (modulesHasDerivedCategory X) (modulesHasDerivedCategory Y)
    (modulesHasDerivedCategory X') (modulesHasDerivedCategory Y')
    (ExactFunctor.of (lowerShriek f)) (ExactFunctor.of (restrictFunctor g))
    (ExactFunctor.of (restrictFunctor h)) (ExactFunctor.of (lowerShriek f'))
    ((exactFunctor X.Modules Y'.Modules).isoMk
      (lowerShriekEtaleBaseChangeNatIso h_cart))

/-- The canonical derived base-change morphism `(j_! E)|_{Y'} ⟶ jW_!(E|_{X'})` in
`D(𝒪_{Y'})`. -/
def derivedLowerShriekEtaleBaseChangeHom (h_cart : IsPullback h f' f g)
    (E : ModuleDerived X) :
    (restrictFunctorDerived g).obj ((lowerShriekDerived f).obj E) ⟶
      (lowerShriekDerived f').obj ((restrictFunctorDerived h).obj E) :=
  (derivedLowerShriekEtaleBaseChangeNatIso h_cart).hom.app E

/-- The identification `(j_! E)|_{Y'} ≅ jW_!(E|_{X'})` in `D(𝒪_{Y'})`. -/
def derivedLowerShriekEtaleBaseChangeIso (h_cart : IsPullback h f' f g)
    (E : ModuleDerived X) :
    (restrictFunctorDerived g).obj ((lowerShriekDerived f).obj E) ≅
      (lowerShriekDerived f').obj ((restrictFunctorDerived h).obj E) :=
  (derivedLowerShriekEtaleBaseChangeNatIso h_cart).app E

/-- The derived étale lower-shriek comparison morphism is an isomorphism. -/
instance isIso_derivedLowerShriekEtaleBaseChangeHom (h_cart : IsPullback h f' f g)
    (E : ModuleDerived X) :
    IsIso (derivedLowerShriekEtaleBaseChangeHom h_cart E) :=
  Iso.isIso_hom (derivedLowerShriekEtaleBaseChangeIso h_cart E)

/-- The forward map of the derived étale lower-shriek isomorphism is the comparison
morphism. -/
theorem derivedLowerShriekEtaleBaseChangeIso_hom (h_cart : IsPullback h f' f g)
    (E : ModuleDerived X) :
    (derivedLowerShriekEtaleBaseChangeIso h_cart E).hom =
      derivedLowerShriekEtaleBaseChangeHom h_cart E :=
  rfl

end BaseChange

variable {V : AlgebraicSpace S}
variable (j : U ⟶ X) [Etale j] (v : V ⟶ X) [Etale v]

/-- Derived extension by zero commutes with étale restriction along the canonical fibre
product, with comparison oriented from restriction to extension by zero. -/
noncomputable abbrev restrictLowerShriekIso (E : ModuleDerived U) :
    (restrictFunctorDerived v).obj ((lowerShriekDerived j).obj E) ≅
      (lowerShriekDerived (Limits.pullback.fst v j)).obj
        ((restrictFunctorDerived (Limits.pullback.snd v j)).obj E) :=
  derivedLowerShriekEtaleBaseChangeIso (IsPullback.of_hasPullback v j).flip E

/-- The forward map of `restrictLowerShriekIso` is the derived lower-shriek comparison
morphism of the flipped canonical pullback square. -/
theorem restrictLowerShriekIso_hom (E : ModuleDerived U) :
    (restrictLowerShriekIso j v E).hom =
      derivedLowerShriekEtaleBaseChangeHom (IsPullback.of_hasPullback v j).flip E :=
  rfl

end AlgebraicGeometry.AlgebraicSpace.Modules
