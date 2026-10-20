module

public import Mathlib.CategoryTheory.Limits.Shapes.Terminal
public import Mathlib.CategoryTheory.ObjectProperty.CompleteLattice
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import ReasLib.Algebra.Category.FGModuleCat.FiniteProducts
public import ReasLib.Algebra.Category.CommAlgCat.Over.SquareZero.FiniteProducts

/-!
# Finitely generated square-zero extensions in `S`-Alg/`R`

The restriction of `M ↦ R[M]` to finitely generated `R`-modules, the object
`R` of `S`-Alg/`R`, and the condition that a strictly full subcategory contains
every `R[M]`.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits ZeroObject

universe u

namespace TrivSqZeroExt

variable (S R : Type u) [CommRing S] [CommRing R] [Algebra S R]

/-- The object `R` of `S`-Alg/`R`, as the identity arrow on `CommAlgCat.of S R`. -/
def overSelf : Over (CommAlgCat.of S R) :=
  Over.mk (𝟙 (CommAlgCat.of S R))

/-- `overSelf` is the identity arrow of `R` in `S`-Alg/`R`. -/
theorem overSelf_eq : overSelf S R = Over.mk (𝟙 (CommAlgCat.of S R)) := rfl

/-- The functor `Mod^{fg}_R ⥤ S`-Alg/`R` sending a finitely generated module `M` to
the trivial square-zero extension `R[M]`. -/
def fgOverFunctor : FGModuleCat.{u} R ⥤ Over (CommAlgCat.of S R) :=
  forget₂ (FGModuleCat.{u} R) (ModuleCat.{u} R) ⋙ overFunctor S R

/-- Objects of `fgOverFunctor` are the square-zero extensions of the underlying
modules. -/
theorem fgOverFunctor_obj (M : FGModuleCat.{u} R) :
    (fgOverFunctor S R).obj M =
      (overFunctor S R).obj ((forget₂ (FGModuleCat.{u} R) (ModuleCat.{u} R)).obj M) :=
  rfl

/-- Morphisms of `fgOverFunctor` are the induced square-zero algebra maps. -/
theorem fgOverFunctor_map {M N : FGModuleCat.{u} R} (f : M ⟶ N) :
    (fgOverFunctor S R).map f =
      (overFunctor S R).map ((forget₂ (FGModuleCat.{u} R) (ModuleCat.{u} R)).map f) :=
  rfl

/-- `fgOverFunctor` is the composite of `forget₂` with `overFunctor`. -/
theorem fgOverFunctor_comp_eq :
    fgOverFunctor S R = forget₂ (FGModuleCat.{u} R) (ModuleCat.{u} R) ⋙ overFunctor S R :=
  rfl

/-- The square-zero extension functor on finitely generated modules preserves finite products. -/
instance fgOverFunctor_preservesFiniteProducts :
    PreservesFiniteProducts (fgOverFunctor S R) := sorry

/-- The canonical algebra map `R ⟶ R[0]` as a morphism of `S`-algebras over `R`. -/
def overSelfToFgOverFunctorZero : overSelf S R ⟶ (fgOverFunctor S R).obj 0 :=
  Over.homMk
    (CommAlgCat.ofHom
      (inlAlgHom S R ((forget₂ (FGModuleCat.{u} R) (ModuleCat.{u} R)).obj 0)))
    sorry

/-- The inverse of `overSelfToFgOverFunctorZero`, as the empty-product comparison
`R[0] ⟶ R` of `overFunctor` transported along `fgOverFunctor_obj`. -/
def fgOverFunctorZeroToOverSelf : (fgOverFunctor S R).obj 0 ⟶ overSelf S R :=
  (eqToIso (fgOverFunctor_obj S R 0)).hom ≫
    (overFunctor S R).map
      (terminal.from ((forget₂ (FGModuleCat.{u} R) (ModuleCat.{u} R)).obj 0)) ≫
    terminalComparison (overFunctor S R) ≫ (terminalIsoIsTerminal Over.mkIdTerminal).hom

/-- `fgOverFunctorZeroToOverSelf` is the transported empty-product comparison. -/
theorem fgOverFunctorZeroToOverSelf_eq :
    fgOverFunctorZeroToOverSelf S R =
      (eqToIso (fgOverFunctor_obj S R 0)).hom ≫
        (overFunctor S R).map
          (terminal.from ((forget₂ (FGModuleCat.{u} R) (ModuleCat.{u} R)).obj 0)) ≫
        terminalComparison (overFunctor S R) ≫
          (terminalIsoIsTerminal Over.mkIdTerminal).hom :=
  rfl

/-- The canonical inclusion followed by the zero-extension projection is the identity on `R`. -/
theorem overSelfToFgOverFunctorZero_comp_inverse :
    overSelfToFgOverFunctorZero S R ≫ fgOverFunctorZeroToOverSelf S R =
      𝟙 (overSelf S R) := sorry

/-- The zero-extension projection followed by the canonical inclusion is the identity on `R[0]`. -/
theorem fgOverFunctorZeroToOverSelf_comp_inverse :
    fgOverFunctorZeroToOverSelf S R ≫ overSelfToFgOverFunctorZero S R =
      𝟙 ((fgOverFunctor S R).obj 0) := sorry

/-- The canonical isomorphism `R ≅ R[0]` in `S`-Alg/`R`. -/
def overSelf_iso_fgOverFunctor_zero : overSelf S R ≅ (fgOverFunctor S R).obj 0 where
  hom := overSelfToFgOverFunctorZero S R
  inv := fgOverFunctorZeroToOverSelf S R
  hom_inv_id := overSelfToFgOverFunctorZero_comp_inverse S R
  inv_hom_id := fgOverFunctorZeroToOverSelf_comp_inverse S R

/-- The forward map of `overSelf_iso_fgOverFunctor_zero` is the canonical algebra
map `R ⟶ R[0]`. -/
theorem overSelf_iso_fgOverFunctor_zero_hom :
    (overSelf_iso_fgOverFunctor_zero S R).hom = overSelfToFgOverFunctorZero S R :=
  rfl

end TrivSqZeroExt

namespace CategoryTheory.ObjectProperty

open TrivSqZeroExt

variable {S R : Type u} [CommRing S] [CommRing R] [Algebra S R]

/-- A property of objects of `S`-Alg/`R` contains every trivial square-zero extension
`R[M]` of a finitely generated `R`-module. -/
@[mk_iff]
class ContainsFGTrivSqZeroExt (P : ObjectProperty (Over (CommAlgCat.of S R))) : Prop where
  /-- Every `R[M]` for `M` finitely generated satisfies `P`. -/
  obj_fgOverFunctor : ∀ M : FGModuleCat.{u} R, P ((fgOverFunctor S R).obj M)

/-- The whole over-category `S`-Alg/`R` contains every `R[M]`. -/
instance instContainsFGTrivSqZeroExt_top :
    (⊤ : ObjectProperty (Over (CommAlgCat.of S R))).ContainsFGTrivSqZeroExt where
  obj_fgOverFunctor _ := trivial

/-- An object `R[M]` of `S`-Alg/`R` satisfies a property that contains all finitely
generated square-zero extensions. -/
instance instIs_fgOverFunctor {P : ObjectProperty (Over (CommAlgCat.of S R))}
    [P.ContainsFGTrivSqZeroExt] {M : FGModuleCat.{u} R} :
    P.Is ((fgOverFunctor S R).obj M) :=
  ⟨ContainsFGTrivSqZeroExt.obj_fgOverFunctor M⟩

/-- The identity object `R` satisfies a strictly full property that contains every
`R[M]`. -/
instance instIs_overSelf {P : ObjectProperty (Over (CommAlgCat.of S R))}
    [P.IsClosedUnderIsomorphisms] [P.ContainsFGTrivSqZeroExt] :
    P.Is (overSelf S R) := sorry

end CategoryTheory.ObjectProperty

namespace TrivSqZeroExt

open CategoryTheory.ObjectProperty

variable {S R : Type u} [CommRing S] [CommRing R] [Algebra S R]
variable {P : ObjectProperty (Over (CommAlgCat.of S R))}

/-- The object `R` of a strictly full subcategory of `S`-Alg/`R` containing every
`R[M]`. -/
def overSelfObj (P : ObjectProperty (Over (CommAlgCat.of S R)))
    [P.IsClosedUnderIsomorphisms] [P.ContainsFGTrivSqZeroExt] :
    P.FullSubcategory where
  obj := overSelf S R
  property := P.prop_of_is (overSelf S R)

/-- The underlying object of `overSelfObj` is `R`. -/
theorem overSelfObj_obj (P : ObjectProperty (Over (CommAlgCat.of S R)))
    [P.IsClosedUnderIsomorphisms] [P.ContainsFGTrivSqZeroExt] :
    (overSelfObj P).obj = overSelf S R := rfl

/-- The restriction `Mod^{fg}_R ⥤ C` of `M ↦ R[M]` through a subcategory containing
every `R[M]`. -/
def fgLift (P : ObjectProperty (Over (CommAlgCat.of S R))) [P.ContainsFGTrivSqZeroExt] :
    FGModuleCat.{u} R ⥤ P.FullSubcategory :=
  P.lift (fgOverFunctor S R) ContainsFGTrivSqZeroExt.obj_fgOverFunctor

/-- Objects of `fgLift` are the square-zero extensions `R[M]` as objects of `C`. -/
theorem fgLift_obj (P : ObjectProperty (Over (CommAlgCat.of S R))) [P.ContainsFGTrivSqZeroExt]
    (M : FGModuleCat.{u} R) :
    ((fgLift P).obj M).obj = (fgOverFunctor S R).obj M := rfl

/-- Composing `fgLift` with the inclusion of `C` recovers `fgOverFunctor`. -/
theorem fgLift_comp_ι (P : ObjectProperty (Over (CommAlgCat.of S R))) [P.ContainsFGTrivSqZeroExt] :
    fgLift P ⋙ P.ι = fgOverFunctor S R := rfl

/-- The canonical morphism `R ⟶ R[0]` in a strictly full subcategory containing every
`R[M]`. -/
def overSelfObjToFgLiftZero (P : ObjectProperty (Over (CommAlgCat.of S R)))
    [P.IsClosedUnderIsomorphisms] [P.ContainsFGTrivSqZeroExt] :
    overSelfObj P ⟶ (fgLift P).obj 0 :=
  homMk (overSelfToFgOverFunctorZero S R)

end TrivSqZeroExt
