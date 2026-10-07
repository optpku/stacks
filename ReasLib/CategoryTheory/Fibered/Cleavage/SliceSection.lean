module

public import Mathlib.CategoryTheory.Comma.Over.Basic
public import ReasLib.CategoryTheory.Fibered.CartesianBasedFunctor.Basic
public import ReasLib.CategoryTheory.Fibered.Cleavage.Basic.Reindex.Functor
import Mathlib.Tactic.CrossRefAttribute

/-!
# Slice sections induced by a cleavage

A cleavage on `p : S ⥤ C` sends an object of the fibre over `U` to a cartesian functor
`C/U ⥤ S`.  This file owns that construction independently of Yoneda evaluation.  The object and
morphism actions are determined by the selected cartesian lifts; only functoriality and
cartesianness proofs are deferred.
-/

@[expose] public section

universe uC vC uS vS

namespace CategoryTheory

open Functor

variable {C : Type uC} [Category.{vC} C]
variable {S : Type uS} [Category.{vS} S]

namespace Functor.Cleavage.SliceSection

variable {p : S ⥤ C}

/-- The arrow between selected pullbacks induced by a morphism in `C/U`. It is the unique
factorization of the cartesian lift over the source slice object through the lift over the
target slice object. -/
@[stacks 0GWI "cleavage slice-section map"]
noncomputable def map (χ : p.Cleavage) {U : C} (x : p.Fiber U)
    {a b : Over U} (φ : a ⟶ b) :
    (χ.reindexObj a.hom x).1 ⟶ (χ.reindexObj b.hom x).1 :=
  -- Local instance justification (defeq pin): use the cartesian witnesses stored by `χ`.
  letI : p.IsStronglyCartesian b.hom (χ.cartesianHom b.hom x) :=
    (χ.reindexLift b.hom x).isStronglyCartesian
  -- Local instance justification (defeq pin): expose the source cartesian lift as a hom lift.
  letI : p.IsHomLift a.hom (χ.cartesianHom a.hom x) :=
    (χ.reindexLift a.hom x).isStronglyCartesian.toIsHomLift
  IsStronglyCartesian.map p b.hom (χ.cartesianHom b.hom x)
    (Over.w φ).symm (χ.cartesianHom a.hom x)

/-- The slice-section map lies over the underlying arrow of the slice morphism. -/
theorem map_isHomLift (χ : p.Cleavage) {U : C} (x : p.Fiber U)
    {a b : Over U} (φ : a ⟶ b) :
    p.IsHomLift φ.left (map χ x φ) := sorry

/-- The slice-section map is characterized by its composite with the selected cartesian lift. -/
@[reassoc]
theorem map_comp_cartesian (χ : p.Cleavage) {U : C} (x : p.Fiber U)
    {a b : Over U} (φ : a ⟶ b) :
    map χ x φ ≫ χ.cartesianHom b.hom x = χ.cartesianHom a.hom x := sorry

/-- A slice-section map is strongly cartesian over the underlying slice arrow. -/
theorem map_isStronglyCartesian (χ : p.Cleavage) {U : C} (x : p.Fiber U)
    {a b : Over U} (φ : a ⟶ b) :
    p.IsStronglyCartesian φ.left (map χ x φ) := sorry

/-- The total-category section of `p` over `C/U` determined by `χ` and `x`. -/
@[stacks 0GWI "cleavage slice section"]
noncomputable def total (χ : p.Cleavage) (U : C) (x : p.Fiber U) : Over U ⥤ S where
  obj a := (χ.reindexObj a.hom x).1
  map φ := map χ x φ
  map_id := sorry
  map_comp := sorry

/-- The slice section sends a slice object to its selected reindexing. -/
@[simp]
theorem total_obj (χ : p.Cleavage) (U : C) (x : p.Fiber U) (a : Over U) :
    (total χ U x).obj a = (χ.reindexObj a.hom x).1 := sorry

/-- The slice section acts on arrows by the canonical cartesian factorization. -/
@[simp]
theorem total_map (χ : p.Cleavage) (U : C) (x : p.Fiber U)
    {a b : Over U} (φ : a ⟶ b) :
    (total χ U x).map φ = map χ x φ := sorry

/-- The total slice section commutes strictly with the projections to `C`. -/
theorem total_comp_projection (χ : p.Cleavage) (U : C) (x : p.Fiber U) :
    total χ U x ⋙ p = Over.forget U := sorry

/-- The slice section packaged as a functor to an existing based-category owner over `C`. -/
@[stacks 0GWI "based cleavage slice section"]
noncomputable def based (Y : BasedCategory.{vS, uS} C) (χ : Y.p.Cleavage)
    (U : C) (x : Y.p.Fiber U) :
    BasedCategory.ofFunctor (Over.forget U) ⥤ᵇ Y where
  toFunctor := total χ U x
  w := total_comp_projection χ U x

/-- A cleavage slice section preserves strongly cartesian arrows. -/
theorem based_preservesStronglyCartesian
    (Y : BasedCategory.{vS, uS} C) (χ : Y.p.Cleavage)
    (U : C) (x : Y.p.Fiber U) :
    (based Y χ U x).PreservesStronglyCartesian := sorry

/-- The slice section at `x`, packaged as a cartesian based functor. -/
@[stacks 0GWI "cartesian cleavage slice section"]
noncomputable def cartesian (Y : BasedCategory.{vS, uS} C) (χ : Y.p.Cleavage)
    (U : C) (x : Y.p.Fiber U) :
    CartesianBasedFunctor (Over.forget U) Y.p :=
  CartesianBasedFunctor.ofBasedFunctor
    (based Y χ U x) (based_preservesStronglyCartesian Y χ U x)

/-- A morphism in the fibre induces a vertical natural transformation between slice sections. -/
noncomputable def natTrans (Y : BasedCategory.{vS, uS} C) (χ : Y.p.Cleavage)
    {U : C} {x y : Y.p.Fiber U} (f : x ⟶ y) :
    based Y χ U x ⟶ based Y χ U y where
  toNatTrans :=
    { app := fun a ↦ (χ.reindexMap a.hom f).1
      naturality := sorry }
  isHomLift' := sorry

/-- The component of the slice-section transformation is the cleavage reindexing map. -/
@[simp]
theorem natTrans_app (Y : BasedCategory.{vS, uS} C) (χ : Y.p.Cleavage)
    {U : C} {x y : Y.p.Fiber U} (f : x ⟶ y) (a : Over U) :
    (natTrans Y χ f).toNatTrans.app a = (χ.reindexMap a.hom f).1 := sorry

/-- The construction of cartesian slice sections is functorial in the fibre object. -/
@[stacks 0GWI "functorial cleavage slice sections"]
noncomputable def functor (Y : BasedCategory.{vS, uS} C) (χ : Y.p.Cleavage) (U : C) :
    Y.p.Fiber U ⥤ CartesianBasedFunctor (Over.forget U) Y.p where
  obj x := cartesian Y χ U x
  map f := CartesianBasedFunctor.homMk (natTrans Y χ f)
  map_id := sorry
  map_comp := sorry

/-!
# Cleavage pullbacks on over-categories

The total-category section above records the chosen reindexing object.  The present namespace
packages the same choice as an actual functor between over-categories.  It is the reusable owner
for cleavage-induced slice pullbacks: object and morphism actions are concrete, while the
universal-property laws are exposed as a small hom-set equivalence and its adjunction.
-/

namespace Pullback

variable {p : S ⥤ C}

/-- The standard-fiber representative of a total-category object. -/
@[stacks 0GWI "cleavage pullback standard fiber"]
abbrev fiber (x : S) : p.Fiber (p.obj x) :=
  Functor.Fiber.mk rfl

/-- The over-object obtained by pulling `A : Over (p.obj x)` back to `x`. -/
@[stacks 0GWI "cleavage pullback object in an over-category"]
noncomputable def obj (χ : p.Cleavage) (x : S) (A : Over (p.obj x)) : Over x :=
  Over.mk (χ.cartesianHom A.hom (fiber (p := p) x))

/-- The underlying object of a cleavage pullback. -/
@[stacks 0GWI "cleavage pullback object projection"]
theorem obj_left (χ : p.Cleavage) (x : S) (A : Over (p.obj x)) :
    (obj χ x A).left = (χ.reindexObj A.hom (fiber (p := p) x)).1 :=
  sorry

/-- The chosen cartesian arrow underlying a cleavage pullback. -/
@[stacks 0GWI "cleavage pullback hom projection"]
theorem obj_hom (χ : p.Cleavage) (x : S) (A : Over (p.obj x)) :
    (obj χ x A).hom = χ.cartesianHom A.hom (fiber (p := p) x) :=
  sorry

/-- The underlying total-category arrow induced by a morphism in the base over-category. -/
@[stacks 0GWI "cleavage pullback underlying map"]
noncomputable def mapHom (χ : p.Cleavage) (x : S) {A B : Over (p.obj x)} (g : A ⟶ B) :
    (obj χ x A).left ⟶ (obj χ x B).left :=
  SliceSection.map χ (fiber (p := p) x) g

/-- The underlying arrow of a cleavage pullback satisfies the over-category factorization law. -/
@[reassoc, stacks 0GWI "cleavage pullback underlying map factorization"]
theorem mapHom_comp_hom (χ : p.Cleavage) (x : S) {A B : Over (p.obj x)} (g : A ⟶ B) :
    mapHom χ x g ≫ (obj χ x B).hom = (obj χ x A).hom := sorry

/-- The cleavage pullback map, bundled as a morphism of over-categories. -/
@[stacks 0GWI "cleavage pullback map"]
noncomputable def map (χ : p.Cleavage) (x : S) {A B : Over (p.obj x)} (g : A ⟶ B) :
    obj χ x A ⟶ obj χ x B :=
  Over.homMk (mapHom χ x g) (mapHom_comp_hom χ x g)

/-- The underlying arrow of the bundled cleavage pullback map. -/
@[simp, stacks 0GWI "cleavage pullback map projection"]
theorem map_left (χ : p.Cleavage) (x : S) {A B : Over (p.obj x)} (g : A ⟶ B) :
    (map χ x g).left = mapHom χ x g := sorry

/-- The cleavage pullback functor between the two over-categories. -/
@[stacks 0GWI "cleavage pullback functor"]
noncomputable def functor (χ : p.Cleavage) (x : S) : Over (p.obj x) ⥤ Over x where
  obj A := obj χ x A
  map g := map χ x g
  map_id := sorry
  map_comp := sorry

/-- The object action of the cleavage pullback functor. -/
@[stacks 0GWI "cleavage pullback functor object"]
theorem functor_obj (χ : p.Cleavage) (x : S) (A : Over (p.obj x)) :
    (functor χ x).obj A = obj χ x A :=
  sorry

/-- The map action of the cleavage pullback functor. -/
@[stacks 0GWI "cleavage pullback functor map"]
theorem functor_map (χ : p.Cleavage) (x : S) {A B : Over (p.obj x)} (g : A ⟶ B) :
    (functor χ x).map g = map χ x g := sorry

/- The following declarations expose endpoint transport and cartesianness once, so downstream
users need not rebuild proof-local instances for every chosen cartesian arrow. -/

/-- The domain of a cleavage pullback object is the domain of its original over-arrow. -/
@[stacks 0GWI "cleavage pullback domain transport"]
theorem obj_domain_eq (χ : p.Cleavage) (x : S) (A : Over (p.obj x)) :
    p.obj (obj χ x A).left = A.left := sorry

/-- The chosen cartesian arrow in a cleavage pullback is strongly cartesian. -/
@[stacks 0GWI "cleavage pullback strong cartesian"]
theorem obj_hom_isStronglyCartesian (χ : p.Cleavage) (x : S) (A : Over (p.obj x)) :
    p.IsStronglyCartesian A.hom (obj χ x A).hom := sorry

/-- The chosen cartesian arrow in a cleavage pullback is a lift of its displayed arrow. -/
@[stacks 0GWI "cleavage pullback hom lift"]
theorem obj_hom_isHomLift (χ : p.Cleavage) (x : S) (A : Over (p.obj x)) :
    p.IsHomLift A.hom (obj χ x A).hom := sorry

/-- The projection of an over-object is a lift of its underlying over-arrow. -/
@[stacks 0GWI "cleavage pullback post hom lift"]
theorem post_isHomLift (x : S) (A : Over x) :
    p.IsHomLift ((Over.post p).obj A).hom A.hom := sorry

/-- The morphism equation used to construct the post-comparison component. -/
@[stacks 0GWI "cleavage pullback post comparison factorization"]
theorem postComponent_fac (χ : p.Cleavage) (x : S) (A : Over (p.obj x)) :
    eqToHom (obj_domain_eq χ x A) ≫ A.hom = p.map (obj χ x A).hom := sorry

/-- The chosen cartesian pullback becomes the original over-object after postcomposition. -/
@[stacks 0GWI "cleavage pullback post-comparison component"]
noncomputable def postComponent (χ : p.Cleavage) (x : S) (A : Over (p.obj x)) :
    (Over.post p).obj (obj χ x A) ≅ A :=
  Over.isoMk (eqToIso (obj_domain_eq χ x A)) (postComponent_fac χ x A)

/-! ### The universal comparison map -/

/-- The ambient arrow obtained by factoring a map into `B` through the chosen cartesian lift. -/
@[stacks 0GWI "cleavage pullback factor map"]
noncomputable def liftFromPost (χ : p.Cleavage) (x : S)
    {A : Over x} {B : Over (p.obj x)}
    (β : (Over.post p).obj A ⟶ B) : A.left ⟶ (obj χ x B).left :=
  @Functor.IsStronglyCartesian.map _ _ _ _ p _ _ _ _
    B.hom (obj χ x B).hom (obj_hom_isStronglyCartesian χ x B) _ _ β.left
    ((Over.post p).obj A).hom (Over.w β).symm A.hom (post_isHomLift (p := p) x A)

/-- The factor map composes with the chosen cartesian arrow to the source over-arrow. -/
@[stacks 0GWI "cleavage pullback factorization"]
theorem liftFromPost_fac (χ : p.Cleavage) (x : S)
    {A : Over x} {B : Over (p.obj x)}
    (β : (Over.post p).obj A ⟶ B) :
    liftFromPost χ x β ≫ (obj χ x B).hom = A.hom := sorry

/-- The factor map lies over the underlying morphism of the base slice arrow. -/
@[stacks 0GWI "cleavage pullback factor hom lift"]
theorem liftFromPost_isHomLift (χ : p.Cleavage) (x : S)
    {A : Over x} {B : Over (p.obj x)}
    (β : (Over.post p).obj A ⟶ B) :
    p.IsHomLift β.left (liftFromPost χ x β) := sorry

/-- The factor map, packaged as a morphism in the over-category of `x`. -/
@[stacks 0GWI "cleavage pullback factor morphism"]
noncomputable def homFromPost (χ : p.Cleavage) (x : S)
    {A : Over x} {B : Over (p.obj x)}
    (β : (Over.post p).obj A ⟶ B) : A ⟶ obj χ x B :=
  Over.homMk (liftFromPost χ x β) (liftFromPost_fac χ x β)

/-- The forward hom-set map from postcomposition to the cleavage pullback. -/
@[stacks 0GWI "cleavage pullback hom-set forward map"]
noncomputable def homForward (χ : p.Cleavage) (x : S)
    {A : Over x} {B : Over (p.obj x)} :
    ((Over.post p).obj A ⟶ B) → (A ⟶ (functor χ x).obj B) :=
  fun β => homFromPost χ x β

/-- The reverse hom-set map induced by the post-comparison component. -/
@[stacks 0GWI "cleavage pullback hom-set reverse map"]
noncomputable def homBackward (χ : p.Cleavage) (x : S)
    {A : Over x} {B : Over (p.obj x)} :
    (A ⟶ (functor χ x).obj B) → ((Over.post p).obj A ⟶ B) :=
  fun γ => (Over.post p).map γ ≫ (postComponent χ x B).hom

/-- The two explicit hom-set maps are inverse in the forward direction. -/
@[stacks 0GWI "cleavage pullback hom-set left inverse"]
theorem homBackward_forward (χ : p.Cleavage) (x : S)
    {A : Over x} {B : Over (p.obj x)} (β : (Over.post p).obj A ⟶ B) :
    homBackward χ x (homForward χ x β) = β := sorry

/-- The two explicit hom-set maps are inverse in the backward direction. -/
@[stacks 0GWI "cleavage pullback hom-set right inverse"]
theorem homForward_backward (χ : p.Cleavage) (x : S)
    {A : Over x} {B : Over (p.obj x)} (γ : A ⟶ (functor χ x).obj B) :
    homForward χ x (homBackward χ x γ) = γ := sorry

/-- The hom-set equivalence exhibiting the cleavage pullback as right adjoint to postcomposition. -/
@[stacks 0GWI "cleavage pullback hom-set equivalence"]
noncomputable def homEquiv (χ : p.Cleavage) (x : S)
    (A : Over x) (B : Over (p.obj x)) :
    (((Over.post p).obj A ⟶ B) ≃ (A ⟶ (functor χ x).obj B)) where
  toFun := homForward χ x
  invFun := homBackward χ x
  left_inv := homBackward_forward χ x
  right_inv := homForward_backward χ x

/-- The cleavage pullback is right adjoint to postcomposition on over-categories. -/
@[stacks 0GWI "cleavage pullback adjunction"]
noncomputable def adjunction (χ : p.Cleavage) (x : S) :
    Over.post p ⊣ functor χ x :=
  Adjunction.mkOfHomEquiv
    { homEquiv := homEquiv χ x
      homEquiv_naturality_left_symm := sorry
      homEquiv_naturality_right := sorry }

/-- The natural post-comparison isomorphism for the cleavage pullback functor. -/
@[stacks 0GWI "cleavage pullback post-comparison isomorphism"]
noncomputable def postIso (χ : p.Cleavage) (x : S) :
    functor χ x ⋙ Over.post p ≅ 𝟭 (Over (p.obj x)) :=
  NatIso.ofComponents (fun A => postComponent χ x A) sorry

end Pullback

end Functor.Cleavage.SliceSection

end CategoryTheory
