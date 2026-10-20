module

public import ReasLib.CategoryTheory.Bicategory.Equivalence
public import ReasLib.CategoryTheory.Fibered.BasedCategory.Basic
public import ReasLib.CategoryTheory.Fibered.BasedCategory.Equivalence.Basic
public import ReasLib.CategoryTheory.Fibered.Equivalence.Fiber
public import ReasLib.CategoryTheory.Fibered.Equivalence.Fiberedness
public import ReasLib.CategoryTheory.Fibered.InGroupoids
import Mathlib.Tactic.CrossRefAttribute

/-!
# Based categories fibred in groupoids

The reusable object property on `BasedCategory C` selecting projections fibred in groupoids,
together with its equivalence and hom-category API. The bundled bicategory of such objects belongs
to the higher-level `FiberedCategoryOver.Groupoids` owner.
-/

@[expose] public section

universe u v w vS

namespace CategoryTheory

open ObjectProperty
open scoped BasedFunctor Bicategory

variable {C : Type u} [Category.{v} C]

namespace BasedNatTrans

universe uX vX uY vY

variable {X : BasedCategory.{vX, uX} C} {Y : BasedCategory.{vY, uY} C}
variable [Functor.IsFibered.InGroupoids Y.p] {F G : X ⥤ᵇ Y}

/-- A vertical component is invertible by the original target's Cartesian
universal property. The native inverse factors the identity through that component. -/
noncomputable def componentIso (α : F ⟶ G) (a : X.obj) :
    F.obj a ≅ G.obj a := by
  letI : Y.p.IsHomLift (𝟙 (X.p.obj a)) (α.toNatTrans.app a) := α.isHomLift' a
  letI : IsIso (Y.p.map (α.toNatTrans.app a)) := by
    rw [IsHomLift.fac' Y.p (𝟙 (X.p.obj a)) (α.toNatTrans.app a)]
    infer_instance
  letI : Y.p.IsStronglyCartesian (Y.p.map (α.toNatTrans.app a))
      (α.toNatTrans.app a) :=
    Functor.IsFibered.isStronglyCartesian_of_isCartesian Y.p
      (Y.p.map (α.toNatTrans.app a)) (α.toNatTrans.app a)
  letI : IsIso (α.toNatTrans.app a) :=
    Functor.IsStronglyCartesian.isIso_of_base_isIso Y.p
      (Y.p.map (α.toNatTrans.app a)) (α.toNatTrans.app a)
  exact asIso (α.toNatTrans.app a)

/-- The component isomorphism has the supplied component as its forward map. -/
@[simp]
theorem componentIso_hom (α : F ⟶ G) (a : X.obj) :
    (componentIso α a).hom = α.toNatTrans.app a := rfl

/-- A based transformation into a category fibred in groupoids has an actual
inverse, assembled from its native Cartesian component inverses. -/
noncomputable def isoOfTargetInGroupoids (α : F ⟶ G) : F ≅ G :=
  BasedNatIso.mkNatIso
    (NatIso.ofComponents (componentIso α) (fun f ↦ α.toNatTrans.naturality f))
    α.isHomLift'

/-- The based isomorphism retains the supplied transformation. -/
@[simp]
theorem isoOfTargetInGroupoids_hom (α : F ⟶ G) :
    (isoOfTargetInGroupoids α).hom = α := rfl

/-- Its inverse uses the explicit native inverse at each component. -/
@[simp]
theorem isoOfTargetInGroupoids_inv_app (α : F ⟶ G) (a : X.obj) :
    (isoOfTargetInGroupoids α).inv.toNatTrans.app a = (componentIso α a).inv := rfl

end BasedNatTrans

namespace BasedFunctor

universe uX vX uY vY

variable {X : BasedCategory.{vX, uX} C} {Y : BasedCategory.{vY, uY} C}

/-- Being fibred in groupoids is invariant under an equivalence over the fixed base. This is the
canonical transport theorem behind repleteness of all later full subbicategories of
`BasedCategory C`. -/
theorem IsEquivalence.inGroupoids_iff
    (F : X ⥤ᵇ Y) [F.IsEquivalence] :
    Functor.IsFibered.InGroupoids X.p ↔ Functor.IsFibered.InGroupoids Y.p := sorry
/- Proof strategy: use `BasedFunctor.IsEquivalence.isFibered_iff F` for the fibredness
component of `Functor.IsFibered.InGroupoids.iff_isFibered_fibersGroupoid`. Transport each domain
fiber's groupoid structure forward with `BasedFunctor.fiberIsGroupoid F`; for the reverse
implication apply the same argument to `F.asQuasiInverse.symm`. -/

/-- If the target projection is fibred in groupoids, the category of based functors into it is a
groupoid. This is the reusable hom-level reason that categories fibred in groupoids form a
`(2,1)`-category.

The inverse of each transformation is stored by
`BasedNatTrans.isoOfTargetInGroupoids`, using the given target's Cartesian factors. -/
instance homGroupoid [Functor.IsFibered.InGroupoids Y.p] : IsGroupoid (X ⥤ᵇ Y) where
  all_isIso α := by
    rw [← BasedNatTrans.isoOfTargetInGroupoids_hom α]
    infer_instance

end BasedFunctor

namespace BasedCategory

/-- The canonical object property selecting based categories
fibred in groupoids. Naming this property preserves the separate hom- and object-universe
parameters of the ambient category; directly inlining the predicate collapses them through the
carrier universe of `FullSubbicategory`. -/
@[stacks 02XS "based-category owner for groupoid-fibred projections"]
abbrev isFiberedInGroupoids (C : Type u) [Category.{v} C] :
    ObjectProperty (BasedCategory.{vS, w} C) :=
  fun X ↦ Functor.IsFibered.InGroupoids X.p

/-- Being fibred in groupoids is invariant under equivalence in the fixed bicategory
`BasedCategory C`. -/
theorem Equivalence.inGroupoids_iff
    {X Y : BasedCategory.{vS, w} C} (e : X ≌ Y) :
    Functor.IsFibered.InGroupoids X.p ↔ Functor.IsFibered.InGroupoids Y.p := sorry
/- Proof strategy: transport fibredness with `BasedCategory.Equivalence.isFibered_iff` and
transport the groupoid structure of every standard fiber with the induced fiber equivalence. -/

namespace isFiberedInGroupoids

/-- Being fibred in groupoids is invariant under equivalence over the fixed base, so this object
property defines a replete full subbicategory. -/
instance isClosedUnderEquivalences
    (C : Type u) [Category.{v} C] :
    (isFiberedInGroupoids C).IsClosedUnderEquivalences := sorry
/- Proof strategy: apply `BasedCategory.Equivalence.inGroupoids_iff` in the forward direction. -/

end isFiberedInGroupoids

end BasedCategory

end CategoryTheory
