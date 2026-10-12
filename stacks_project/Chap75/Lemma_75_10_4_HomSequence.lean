/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Homology.ExactSequence
public import Mathlib.CategoryTheory.Adjunction.Additive
public import Mathlib.CategoryTheory.ComposableArrows.Three
public import Mathlib.CategoryTheory.Limits.Shapes.Biproducts
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import ReasLib.Algebra.Homology.DerivedCategory.Adjunction
public import ReasLib.CategoryTheory.DerivedCategory.Ext
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Exact.Composition
public import ReasLib.CategoryTheory.Shift.ShiftedHom.Adjunction
public import ReasLib.CategoryTheory.Shift.ShiftedHom.Equiv
public import stacks_project.Chap75.Lemma_75_10_1_Sequence

/-!
# Mayer–Vietoris Hom-group maps in `D(𝒪)` of algebraic spaces

Étale lower shriek is left adjoint to étale restriction on unbounded derived
categories. Restriction, signed overlap difference, and a connecting map built
from a triangle morphism `δ` give the three arrows of the Hom/Ext segment of
Lemma 75.10.4.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules CategoryTheory.Limits
open CategoryTheory.Preadditive CategoryTheory.Functor
open AlgebraicGeometry.AlgebraicSpace.SmallEtaleModuleGlueing (restrictFunctorComp)
open scoped DerivedExt

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

variable {S : Scheme.{u}} {U X : AlgebraicSpace S}

/-- The derived adjunction `j_! ⊣ j^*` induced by étale extension by zero of
modules on algebraic spaces. -/
def lowerShriekDerivedAdjunction (f : U ⟶ X) [Etale f] :
    lowerShriekDerived f ⊣ restrictFunctorDerived f :=
  Adjunction.mapDerivedCategory (lowerShriekAdjunction f)

/-- The Hom-equivalence `Hom(j_! E, F) ≃ Hom(E, F|_U)` of
`lowerShriekDerivedAdjunction`. -/
def lowerShriekDerivedAdjunction_homEquiv (f : U ⟶ X) [Etale f]
    (E : ModuleDerived U) (F : ModuleDerived X) :
    ((lowerShriekDerived f).obj E ⟶ F) ≃
      (E ⟶ (restrictFunctorDerived f).obj F) :=
  (lowerShriekDerivedAdjunction f).homEquiv E F

namespace lowerShriekDerived

/-- Derived étale lower shriek is a left adjoint. -/
instance instIsLeftAdjoint (f : U ⟶ X) [Etale f] :
    (lowerShriekDerived f).IsLeftAdjoint :=
  (lowerShriekDerivedAdjunction f).isLeftAdjoint

end lowerShriekDerived

namespace restrictFunctorDerived

/-- Derived étale restriction is a right adjoint. -/
instance instIsRightAdjoint (f : U ⟶ X) [Etale f] :
    (restrictFunctorDerived f).IsRightAdjoint :=
  (lowerShriekDerivedAdjunction f).isRightAdjoint

end restrictFunctorDerived

variable {V : AlgebraicSpace S}
variable (j : U ⟶ X) [Etale j] (f : V ⟶ X) [Etale f]

/-- Passage of derived restriction through composition of exact functors. -/
def restrictFunctorDerivedSuccessiveIso {W : AlgebraicSpace S} (p : W ⟶ U) [Etale p] :
    ((ExactFunctor.of (restrictFunctor j)).comp
        (ExactFunctor.of (restrictFunctor p))).mapDerivedCategory ≅
      restrictFunctorDerived j ⋙ restrictFunctorDerived p :=
  ExactFunctor.MapDerivedCategory.compFunctorIso
    (ExactFunctor.of (restrictFunctor j)) (ExactFunctor.of (restrictFunctor p))

/-- Derived restriction along an étale composite is the composite of the derived
restrictions. -/
def restrictFunctorDerivedCompIso {W : AlgebraicSpace S} (p : W ⟶ U) [Etale p] :
    restrictFunctorDerived j ⋙ restrictFunctorDerived p ≅
      restrictFunctorDerived (p ≫ j) :=
  (restrictFunctorDerivedSuccessiveIso j p).symm ≪≫
    ExactFunctor.MapDerivedCategory.mapIso
      ((exactFunctor X.Modules W.Modules).isoMk (Iso.refl _)) ≪≫
    Functor.MapDerivedCategory.functorIso (restrictFunctorComp p j)

/-- Transport derived restriction along an equality of étale morphisms. -/
def restrictFunctorDerived_eqToIso {W : AlgebraicSpace S} {p q : W ⟶ X}
    [Etale p] [Etale q] (h : p = q) :
    restrictFunctorDerived p ≅ restrictFunctorDerived q :=
  h ▸ Iso.refl (restrictFunctorDerived p)

/-- Restriction of Hom-groups from `D(𝒪_U)` to `D(𝒪_W)` along an étale
factorization `W ⟶ U ⟶ X`, identified with restriction along the composite. -/
def mayerVietorisHomRestrictLeg {W : AlgebraicSpace S} (p : W ⟶ U) [Etale p]
    (E F : ModuleDerived X) :
    AddCommGrpCat.of
        ((restrictFunctorDerived j).obj E ⟶ (restrictFunctorDerived j).obj F) ⟶
      AddCommGrpCat.of
        ((restrictFunctorDerived (p ≫ j)).obj E ⟶
          (restrictFunctorDerived (p ≫ j)).obj F) :=
  AddCommGrpCat.ofHom <|
    (leftComp _ ((restrictFunctorDerivedCompIso j p).inv.app E)).comp <|
      (rightComp _ ((restrictFunctorDerivedCompIso j p).hom.app F)).comp
        (restrictFunctorDerived p).mapAddHom

/-- The first visible Mayer–Vietoris arrow
`Hom(E, F) ⟶ Hom(E|_U, F|_U) ⊞ Hom(E|_V, F|_V)` of restriction maps. -/
def mayerVietorisHomRestrict (E F : ModuleDerived X) :
    AddCommGrpCat.of (E ⟶ F) ⟶
      biprod (AddCommGrpCat.of
          ((restrictFunctorDerived j).obj E ⟶ (restrictFunctorDerived j).obj F))
        (AddCommGrpCat.of
          ((restrictFunctorDerived f).obj E ⟶ (restrictFunctorDerived f).obj F)) :=
  biprod.lift
    (AddCommGrpCat.ofHom
      ((restrictFunctorDerived j).mapAddHom : (E ⟶ F) →+ _))
    (AddCommGrpCat.ofHom
      ((restrictFunctorDerived f).mapAddHom : (E ⟶ F) →+ _))

/-- Conjugation of Hom-groups by an equality of étale morphisms to `X`. -/
def mayerVietorisHomCongr {W : AlgebraicSpace S} {p q : W ⟶ X}
    [Etale p] [Etale q] (h : p = q) (E F : ModuleDerived X) :
    AddCommGrpCat.of
        ((restrictFunctorDerived p).obj E ⟶ (restrictFunctorDerived p).obj F) ⟶
      AddCommGrpCat.of
        ((restrictFunctorDerived q).obj E ⟶ (restrictFunctorDerived q).obj F) :=
  AddCommGrpCat.ofHom <|
    (leftComp _ ((restrictFunctorDerived_eqToIso h).inv.app E)).comp
      (rightComp _ ((restrictFunctorDerived_eqToIso h).hom.app F))

/-- The second visible Mayer–Vietoris arrow
`Hom(E|_U, F|_U) ⊞ Hom(E|_V, F|_V) ⟶ Hom(E|_W, F|_W)`, with a minus sign on the
`V`-leg, for `W = U ×_X V`. -/
def mayerVietorisHomDiff (E F : ModuleDerived X) :
    biprod (AddCommGrpCat.of
          ((restrictFunctorDerived j).obj E ⟶ (restrictFunctorDerived j).obj F))
        (AddCommGrpCat.of
          ((restrictFunctorDerived f).obj E ⟶ (restrictFunctorDerived f).obj F)) ⟶
      AddCommGrpCat.of
        ((restrictFunctorDerived (fiberHom j f)).obj E ⟶
          (restrictFunctorDerived (fiberHom j f)).obj F) :=
  biprod.desc (mayerVietorisHomRestrictLeg j (Limits.pullback.fst j f) E F)
    (-(mayerVietorisHomRestrictLeg f (Limits.pullback.snd j f) E F ≫
      mayerVietorisHomCongr (fiberHom_eq j f).symm E F))

/-- Additivity of the connecting Hom-group formula of `mayerVietorisHomδ`. -/
theorem mayerVietorisHomδ_map_add (E F : ModuleDerived X)
    (δ : E ⟶
      ((lowerShriekDerived (fiberHom j f)).obj
          ((restrictFunctorDerived (fiberHom j f)).obj E))⟦(1 : ℤ)⟧)
    (α β : Ext⁽(-1 : ℤ)⁾((restrictFunctorDerived (fiberHom j f)).obj E,
      (restrictFunctorDerived (fiberHom j f)).obj F)) :
    (δ ≫
        ShiftedHom.sourceShiftEquiv
          ((lowerShriekDerived (fiberHom j f)).obj
            ((restrictFunctorDerived (fiberHom j f)).obj E))
          F (-1)
          ((lowerShriekDerivedAdjunction (fiberHom j f)).shiftedHomEquiv
            ((restrictFunctorDerived (fiberHom j f)).obj E) F (-1) (α + β))) =
      (δ ≫
          ShiftedHom.sourceShiftEquiv
            ((lowerShriekDerived (fiberHom j f)).obj
              ((restrictFunctorDerived (fiberHom j f)).obj E))
            F (-1)
            ((lowerShriekDerivedAdjunction (fiberHom j f)).shiftedHomEquiv
              ((restrictFunctorDerived (fiberHom j f)).obj E) F (-1) α)) +
        (δ ≫
          ShiftedHom.sourceShiftEquiv
            ((lowerShriekDerived (fiberHom j f)).obj
              ((restrictFunctorDerived (fiberHom j f)).obj E))
            F (-1)
            ((lowerShriekDerivedAdjunction (fiberHom j f)).shiftedHomEquiv
              ((restrictFunctorDerived (fiberHom j f)).obj E) F (-1) β)) :=
  sorry

/-- The connecting Hom-group map
`Ext⁽-1⁾(E|_W, F|_W) ⟶ Hom(E, F)` associated to a morphism
`δ : E ⟶ j_{W!}(E|_W)⟦1⟧`. -/
def mayerVietorisHomδ (E F : ModuleDerived X)
    (δ : E ⟶
      ((lowerShriekDerived (fiberHom j f)).obj
          ((restrictFunctorDerived (fiberHom j f)).obj E))⟦(1 : ℤ)⟧) :
    AddCommGrpCat.of
        (Ext⁽(-1 : ℤ)⁾((restrictFunctorDerived (fiberHom j f)).obj E,
          (restrictFunctorDerived (fiberHom j f)).obj F)) ⟶
      AddCommGrpCat.of (E ⟶ F) :=
  AddCommGrpCat.ofHom <|
    AddMonoidHom.mk'
      (fun α ↦
        δ ≫
          ShiftedHom.sourceShiftEquiv
            ((lowerShriekDerived (fiberHom j f)).obj
              ((restrictFunctorDerived (fiberHom j f)).obj E))
            F (-1)
            ((lowerShriekDerivedAdjunction (fiberHom j f)).shiftedHomEquiv
              ((restrictFunctorDerived (fiberHom j f)).obj E) F (-1) α))
      (mayerVietorisHomδ_map_add j f E F δ)

/-- The `U`-component of `mayerVietorisHomRestrict` is derived restriction along
`j`. -/
theorem mayerVietorisHomRestrict_fst (E F : ModuleDerived X) :
    mayerVietorisHomRestrict j f E F ≫ biprod.fst =
      AddCommGrpCat.ofHom
        ((restrictFunctorDerived j).mapAddHom : (E ⟶ F) →+ _) :=
  sorry

/-- The `V`-component of `mayerVietorisHomRestrict` is derived restriction along
`f`. -/
theorem mayerVietorisHomRestrict_snd (E F : ModuleDerived X) :
    mayerVietorisHomRestrict j f E F ≫ biprod.snd =
      AddCommGrpCat.ofHom
        ((restrictFunctorDerived f).mapAddHom : (E ⟶ F) →+ _) :=
  sorry

/-- The `U`-leg of `mayerVietorisHomDiff` is restriction from `U` to
`W = U ×_X V`. -/
theorem mayerVietorisHomDiff_inl (E F : ModuleDerived X) :
    biprod.inl ≫ mayerVietorisHomDiff j f E F =
      mayerVietorisHomRestrictLeg j (Limits.pullback.fst j f) E F :=
  sorry

/-- The `V`-leg of `mayerVietorisHomDiff` is minus restriction from `V` to
`W = U ×_X V`. -/
theorem mayerVietorisHomDiff_inr (E F : ModuleDerived X) :
    biprod.inr ≫ mayerVietorisHomDiff j f E F =
      -(mayerVietorisHomRestrictLeg f (Limits.pullback.snd j f) E F ≫
        mayerVietorisHomCongr (fiberHom_eq j f).symm E F) :=
  sorry

/-- `mayerVietorisHomδ` is precomposition with `δ` after transporting
`Ext⁽-1⁾(E|_W, F|_W)` through the derived adjunction and the source-shift
identification with morphisms `j_{W!}(E|_W)⟦1⟧ ⟶ F`. -/
theorem mayerVietorisHomδ_eq (E F : ModuleDerived X)
    (δ : E ⟶
      ((lowerShriekDerived (fiberHom j f)).obj
          ((restrictFunctorDerived (fiberHom j f)).obj E))⟦(1 : ℤ)⟧)
    (α : Ext⁽(-1 : ℤ)⁾((restrictFunctorDerived (fiberHom j f)).obj E,
      (restrictFunctorDerived (fiberHom j f)).obj F)) :
    mayerVietorisHomδ j f E F δ α =
      δ ≫
        ShiftedHom.sourceShiftEquiv
          ((lowerShriekDerived (fiberHom j f)).obj
            ((restrictFunctorDerived (fiberHom j f)).obj E))
          F (-1)
          ((lowerShriekDerivedAdjunction (fiberHom j f)).shiftedHomEquiv
            ((restrictFunctorDerived (fiberHom j f)).obj E) F (-1) α) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules
