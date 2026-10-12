/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.CategoryTheory.Endomorphism
public import Mathlib.CategoryTheory.Yoneda
public import ReasLib.AlgebraicGeometry.Scheme.OverField
public import ReasLib.AlgebraicGeometry.Scheme.Variety.Curve

/-!
# Automorphism functor of a scheme over a field

The group-valued functor of points sending `T` to `Aut_T(X_T)`, together with
its object/map normal forms and representability for proper curves.
-/

@[expose] public section

open CategoryTheory Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.SchemeOverField

variable {k : Type u} [Field k] (X : SchemeOverField k)

/-- The automorphism group of the base change of `X` to an object of `Over (Spec k)`. -/
def autFunctorObj (T : (Over (Spec (CommRingCat.of k)))ᵒᵖ) : GrpCat.{u} :=
  GrpCat.of (Aut ((Over.pullback (unop T).hom).obj X))

/-- The value of `autFunctorObj` is the automorphism group of the pulled-back object. -/
theorem autFunctorObj_eq (T : (Over (Spec (CommRingCat.of k)))ᵒᵖ) :
    autFunctorObj X T = GrpCat.of (Aut ((Over.pullback (unop T).hom).obj X)) := sorry

/-- The comparison identifying the iterated pullback of `X` along a morphism of bases
with the direct pullback to the source. -/
def autFunctorPullbackIso {T T' : (Over (Spec (CommRingCat.of k)))ᵒᵖ} (f : T ⟶ T') :
    (Over.pullback f.unop.left).obj ((Over.pullback (unop T).hom).obj X) ≅
      (Over.pullback (unop T').hom).obj X :=
  ((Over.pullbackComp f.unop.left (unop T).hom).app X).symm ≪≫
    eqToIso (congrArg
      (fun h : (unop T').left ⟶ Spec (CommRingCat.of k) => (Over.pullback h).obj X)
      f.unop.w)

/-- `autFunctorPullbackIso` is the `Over.pullbackComp` comparison transported along the
triangle equality of the base morphism. -/
theorem autFunctorPullbackIso_eq {T T' : (Over (Spec (CommRingCat.of k)))ᵒᵖ} (f : T ⟶ T') :
    autFunctorPullbackIso X f =
      ((Over.pullbackComp f.unop.left (unop T).hom).app X).symm ≪≫
        eqToIso (congrArg
          (fun h : (unop T').left ⟶ Spec (CommRingCat.of k) => (Over.pullback h).obj X)
          f.unop.w) := sorry

/-- Base change of automorphisms along a morphism of bases, as a group homomorphism. -/
def autFunctorMapHom {T T' : (Over (Spec (CommRingCat.of k)))ᵒᵖ} (f : T ⟶ T') :
    Aut ((Over.pullback (unop T).hom).obj X) →*
      Aut ((Over.pullback (unop T').hom).obj X) :=
  (Aut.autMulEquivOfIso (autFunctorPullbackIso X f)).toMonoidHom.comp
    (Functor.mapAut ((Over.pullback (unop T).hom).obj X) (Over.pullback f.unop.left))

/-- `autFunctorMapHom` conjugates the image of `Functor.mapAut` along `autFunctorPullbackIso`. -/
theorem autFunctorMapHom_apply {T T' : (Over (Spec (CommRingCat.of k)))ᵒᵖ} (f : T ⟶ T')
    (α : Aut ((Over.pullback (unop T).hom).obj X)) :
    autFunctorMapHom X f α =
      Aut.autMulEquivOfIso (autFunctorPullbackIso X f)
        ((Over.pullback f.unop.left).mapIso α) := sorry

/-- The `GrpCat` morphism induced by base change of automorphisms. -/
def autFunctorMap {T T' : (Over (Spec (CommRingCat.of k)))ᵒᵖ} (f : T ⟶ T') :
    autFunctorObj X T ⟶ autFunctorObj X T' :=
  GrpCat.ofHom (autFunctorMapHom X f)

/-- Base change of automorphisms preserves identity morphisms. -/
theorem autFunctorMap_id (T : (Over (Spec (CommRingCat.of k)))ᵒᵖ) :
    autFunctorMap X (𝟙 T) = 𝟙 (autFunctorObj X T) := sorry

/-- Base change of automorphisms preserves composition. -/
theorem autFunctorMap_comp {T T' T'' : (Over (Spec (CommRingCat.of k)))ᵒᵖ}
    (f : T ⟶ T') (g : T' ⟶ T'') :
    autFunctorMap X (f ≫ g) = autFunctorMap X f ≫ autFunctorMap X g := sorry

/-- The group-valued functor of points `T ↦ Aut_T(X_T)` of a scheme over a field. -/
def autFunctor : (Over (Spec (CommRingCat.of k)))ᵒᵖ ⥤ GrpCat.{u} where
  obj := autFunctorObj X
  map := autFunctorMap X
  map_id := autFunctorMap_id X
  map_comp := autFunctorMap_comp X

/-- On objects, `autFunctor X` evaluates to automorphisms of the base change of `X`. -/
theorem autFunctor_obj (T : (Over (Spec (CommRingCat.of k)))ᵒᵖ) :
    (autFunctor X).obj T = GrpCat.of (Aut ((Over.pullback (unop T).hom).obj X)) := sorry

/-- On morphisms, `autFunctor X` acts by the constructed base-change group homomorphism. -/
theorem autFunctor_map {T T' : (Over (Spec (CommRingCat.of k)))ᵒᵖ} (f : T ⟶ T') :
    (autFunctor X).map f = GrpCat.ofHom (autFunctorMapHom X f) := sorry

/-- The automorphism functor of a proper curve over a field is representable. -/
instance autFunctor_isRepresentable [Curve X] [IsProper X.hom] :
    (autFunctor X ⋙ forget GrpCat).IsRepresentable := sorry

end AlgebraicGeometry.SchemeOverField
