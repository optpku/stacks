module

public import Mathlib.CategoryTheory.Endomorphism
public import Mathlib.CategoryTheory.Yoneda
public import ReasLib.CategoryTheory.Cofibered.InGroupoids
public import ReasLib.CategoryTheory.Cofibered.Grothendieck
public import ReasLib.CategoryTheory.Cofibered.FiberIsoClass
public import ReasLib.CategoryTheory.Cofibered.Pushforward
public import ReasLib.CategoryTheory.Cofibered.Restriction
public import ReasLib.CategoryTheory.Cofibered.Pseudofunctor
public import ReasLib.CategoryTheory.Fibered.TwoFibreProduct.FullSubbicategory.Bilimit
import StacksCheckRecall

@[expose] public section

universe u v w vS vB uF vF

namespace CategoryTheory

open Opposite Functor Bicategory
open scoped Bicategory BasedFunctor TwoFibreProduct

variable {C : Type u} [Category.{v} C]
variable {F : Type uF} [Category.{vF} F]
variable (p : F ⥤ C)

/- Remarks 90.5.2: categories cofibered in groupoids and their canonical constructions.
(1) The projection `p : F ⥤ C` is often omitted from the notation. -/
@[stacks 06GK] #check (CategoryTheory.CofiberedCategoryOver.Groupoids.{u, v, w, vS} C :
  Type max (w + 1) (vS + 1) u v)

/- Clause (2): `F(U)` is `p.Fiber U`, with objects over `U` and morphisms over `𝟙 U`;
`Mor_U(x,y)` is the hom type in that fibre. -/
#check (CategoryTheory.Functor.Fiber p : C → Type uF)

/- Clause (3): fibres are groupoids, so all their morphisms are isomorphisms;
`Aut_U(x)` denotes all self-morphisms of a fibre object, represented by `End x`. -/
#check (CategoryTheory.Functor.IsFibered.InGroupoids.fiberIsGroupoid_of_cofibered :
  {F : Type uF} → [Category.{vF} F] → (q : F ⥤ C) → [IsFibered.InGroupoids q.op] →
    (U : C) → IsGroupoid (q.Fiber U))
variable (U : C) (x : p.Fiber U)
#check (CategoryTheory.End x : Type vF)

/- Clause (4): pushforwards are arrows lying over a base morphism; they are unique
up to unique vertical isomorphism. The chosen target is denoted `f_*x`. -/
#check (CategoryTheory.Functor.pushforward_unique :
  {F : Type uF} → [Category.{vF} F] → {q : F ⥤ C} → [IsFibered.InGroupoids q.op] →
    {U V : C} → {x y y' : F} → (f : U ⟶ V) →
      (φ : x ⟶ y) → (ψ : x ⟶ y') → [q.IsHomLift f φ] → [q.IsHomLift f ψ] →
        ∃! τ : y ⟶ y', q.IsHomLift (𝟙 V) τ ∧ φ ≫ τ = ψ ∧ IsIso τ)

/- Clause (5): a choice of pushforwards is a cleavage of `p.op`, available by choice. -/
#check (CategoryTheory.Functor.cleavageOp :
  (q : F ⥤ C) → [IsFibered.InGroupoids q.op] → q.op.Cleavage)

/- Clause (6): a choice of pushforwards yields a covariant pseudofunctor with the
standard groupoid fibres and the chosen pushforward fibre functors. -/
#check (CategoryTheory.Functor.existsPushforwardPseudofunctor :
  (q : F ⥤ C) → [IsFibered.InGroupoids q.op] → (χ : q.op.Cleavage) →
    ∃ P : LocallyDiscrete C ⥤ᵖ Cat.{vF, uF},
      (∀ U : C, P.obj (LocallyDiscrete.mk U) = Cat.of (q.Fiber U)) ∧
      (∀ {U V : C} (f : U ⟶ V),
        HEq (P.map f.toLoc) (Functor.pushforwardFiberFunctor q χ f).toCatHom))

section Morphisms
variable {X Y : CofiberedCategoryOver.Groupoids.{u, v, w, vS} C} (φ : X ⟶ Y)
/- Clause (7): `Mor_C(X,Y)` consists of functors commuting with the projections. -/
#check (CategoryTheory.CofiberedCategoryOver.Groupoids.toBasedFunctor φ :
  X.toBasedCategory ⥤ᵇ Y.toBasedCategory)
#check (CategoryTheory.CofiberedCategoryOver.Groupoids.comm φ :
  CofiberedCategoryOver.Groupoids.toFunctor φ ⋙ Y.p = X.p)

/- Clause (8): `Cof(C)` is a `(2,1)`-category; two-cells are natural transformations
whose components lie over identity base arrows. -/
#check (CategoryTheory.CofiberedCategoryOver.Groupoids.locallyGroupoid :
  IsLocallyGroupoid (CofiberedCategoryOver.Groupoids.{u, v, w, vS} C))
variable {ψ : X ⟶ Y} (η : φ ⟶ ψ) (a : X.total)
#check (CategoryTheory.CofiberedCategoryOver.Groupoids.TwoCell.app.isHomLiftId η a :
  Functor.IsHomLift Y.p (𝟙 (X.p.obj a))
    ((CofiberedCategoryOver.Groupoids.toNatTrans η).app a))
end Morphisms

/- Clause (9): a groupoid-valued functor realizes as a cofibered category, with objects
`(U,x)`, morphisms `(f,a)` where `a : F(f)(x) ⟶ y`, and projection `(U,x) ↦ U`. -/
#check (CategoryTheory.Functor.ofGroupoidValued :
  (C ⥤ Grpd.{vS, w}) → CofiberedCategoryOver.Groupoids.{u, v, max u w, max v vS} C)

/- Clause (10): fibrewise isomorphism classes form a covariant functor, independent
of the choice of pushforward; a cofibered morphism induces a natural transformation. -/
#check (CategoryTheory.Functor.fiberIsoClassFunctor :
  (q : F ⥤ C) → [IsFibered.InGroupoids q.op] → (C ⥤ Type uF))
variable {X Y : CofiberedCategoryOver.Groupoids.{u, v, uF, vF} C} (φ : X ⟶ Y)
#check (CategoryTheory.CofiberedCategoryOver.Groupoids.fiberIsoClassFunctorMap φ :
  Functor.fiberIsoClassFunctor X.p ⟶ Functor.fiberIsoClassFunctor Y.p)

/- Clause (11): discrete groupoids realize set-valued functors as categories cofibered
in sets; this embedding is fully faithful, identifying the functors and their morphisms. -/
#check (CategoryTheory.Functor.ofTypeValuedFunctor :
  (C ⥤ Type w) ⥤ CofiberedCategoryOver.Groupoids.{u, v, max u w, v} C)
#check (CategoryTheory.Functor.ofTypeValuedMap.bijective :
  {F G : C ⥤ Type w} →
    Function.Bijective (Functor.ofTypeValuedMap : (F ⟶ G) →
      (Functor.ofTypeValued F ⟶ Functor.ofTypeValued G)))

/- Clause (12): `underline U = Mor_C(U,-)` is the covariant representable;
`coyoneda` embeds `Cᵒᵖ` fully faithfully, taking `f : U ⟶ V` to `underline V ⟶ underline U`. -/
#check (CategoryTheory.coyoneda : Cᵒᵖ ⥤ C ⥤ Type v)
#check (CategoryTheory.Coyoneda.fullyFaithful :
  (coyoneda : Cᵒᵖ ⥤ C ⥤ Type v).FullyFaithful)

section TwoFibreProducts
variable {X Y S : CofiberedCategoryOver.Groupoids.{u, v, max w (max u (max v vB)), max v vB} C}
variable (φ : X ⟶ S) (ψ : Y ⟶ S)
/- Clause (13): two-fibre products are the explicit based pseudo-pullbacks, including
their projections, comparison isomorphism, and universal property. -/
#check (CategoryTheory.TwoFibreProduct.apex φ ψ :
  CofiberedCategoryOver.Groupoids.{u, v, max w (max u (max v vB)), max v vB} C)
#check (CategoryTheory.TwoFibreProduct.cone φ ψ : PseudoPullbackCone φ ψ)
#check (CategoryTheory.TwoFibreProduct.cone.isBilimit φ ψ :
  (TwoFibreProduct.cone φ ψ).IsBilimit)
end TwoFibreProducts

/- Clause (14): the product is the two-fibre product over the identity cofibered category. -/
#check (CategoryTheory.CofiberedCategoryOver.Groupoids.product :
  CofiberedCategoryOver.Groupoids.{u, v, max w (max u (max v vB)), max v vB} C →
    CofiberedCategoryOver.Groupoids.{u, v, max w (max u (max v vB)), max v vB} C →
      CofiberedCategoryOver.Groupoids.{u, v, max w (max u (max v vB)), max v vB} C)

/- Clause (15): restriction to a full base subcategory is the full subcategory on objects
lying over it, with the induced projection remaining cofibered in groupoids. -/
variable (X : CofiberedCategoryOver.Groupoids.{u, v, uF, vF} C) (P : ObjectProperty C)
#check (CategoryTheory.CofiberedCategoryOver.Groupoids.restrictTo X P :
  CofiberedCategoryOver.Groupoids.{u, v, uF, vF} P.FullSubcategory)
#check (CategoryTheory.Functor.restrictTo.isCofibered X.p P :
  IsFibered.InGroupoids (Functor.restrictTo X.p P).op)

end CategoryTheory
