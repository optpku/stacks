/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Adjunction.Mates
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Exact.Square
public import stacks_project.Chap67.«67_11_1_1_Comparison»
public import stacks_project.Chap75.Lemma_75_10_6_LowerShriek

/-!
# Étale base change for derived lower shriek of modules

A cartesian square of algebraic spaces with étale edges induces a canonical identification
`(j_! E)|_V ≅ jW_!(E|_W)` in `D(𝒪_V)`. The underived comparison is the mate of the
forward pushforward Beck--Chevalley morphism of the flipped square along `j_! ⊣ j^*` and
`j^* ⊣ j_*`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules CategoryTheory.Limits CategoryTheory.Functor

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

variable {S : Scheme.{u}} {X' X Y' Y : AlgebraicSpace S}
variable {h : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
variable [Etale f] [Etale f'] [Etale g] [Etale h]

/-- The underived étale lower-shriek comparison 2-cell, obtained as the mate of the forward
pushforward Beck--Chevalley morphism of the flipped cartesian square. -/
def lowerShriekEtaleBaseChangeNatTrans (h_cart : IsPullback h f' f g) :
    restrictFunctor h ⋙ lowerShriek f' ⟶ lowerShriek f ⋙ restrictFunctor g :=
  (conjugateEquiv
      ((lowerShriekAdjunction f).comp (restrictAdjunction g))
      ((restrictAdjunction h).comp (lowerShriekAdjunction f'))).symm
    (pushforwardEtaleBaseChangeNatTrans h_cart.flip)

/-- The mate of the forward pushforward comparison is an isomorphism. -/
instance isIso_lowerShriekEtaleBaseChangeNatTrans_app (h_cart : IsPullback h f' f g)
    (F : X.Modules) :
    IsIso ((lowerShriekEtaleBaseChangeNatTrans h_cart).app F) :=
  sorry

/-- The canonical underived base-change morphism `(j_! F)|_{Y'} ⟶ jW_!(F|_{X'})` of sheaves of
modules, obtained by orienting the mate of the forward pushforward comparison. -/
def lowerShriekEtaleBaseChangeHom (h_cart : IsPullback h f' f g) (F : X.Modules) :
    (restrictFunctor g).obj ((lowerShriek f).obj F) ⟶
      (lowerShriek f').obj ((restrictFunctor h).obj F) :=
  (asIso ((lowerShriekEtaleBaseChangeNatTrans h_cart).app F)).inv

/-- The identification `(j_! F)|_{Y'} ≅ jW_!(F|_{X'})` of sheaves of modules. -/
def lowerShriekEtaleBaseChangeIso (h_cart : IsPullback h f' f g) (F : X.Modules) :
    (restrictFunctor g).obj ((lowerShriek f).obj F) ≅
      (lowerShriek f').obj ((restrictFunctor h).obj F) :=
  (asIso ((lowerShriekEtaleBaseChangeNatTrans h_cart).app F)).symm

/-- The underived étale lower-shriek comparison morphism is an isomorphism. -/
instance isIso_lowerShriekEtaleBaseChangeHom (h_cart : IsPullback h f' f g)
    (F : X.Modules) :
    IsIso (lowerShriekEtaleBaseChangeHom h_cart F) :=
  Iso.isIso_hom (lowerShriekEtaleBaseChangeIso h_cart F)

/-- The underived étale lower-shriek Beck--Chevalley isomorphism of module functors. -/
def lowerShriekEtaleBaseChangeNatIso (h_cart : IsPullback h f' f g) :
    lowerShriek f ⋙ restrictFunctor g ≅ restrictFunctor h ⋙ lowerShriek f' :=
  NatIso.ofComponents (fun F ↦ lowerShriekEtaleBaseChangeIso h_cart F) sorry

/-- The forward map of the underived étale lower-shriek isomorphism is the comparison
morphism. -/
theorem lowerShriekEtaleBaseChangeIso_hom (h_cart : IsPullback h f' f g)
    (F : X.Modules) :
    (lowerShriekEtaleBaseChangeIso h_cart F).hom =
      lowerShriekEtaleBaseChangeHom h_cart F :=
  rfl

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

end AlgebraicGeometry.AlgebraicSpace.Modules
