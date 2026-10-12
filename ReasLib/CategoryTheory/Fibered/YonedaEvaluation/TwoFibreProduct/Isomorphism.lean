/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.HomPresheaf.Isom
public import ReasLib.CategoryTheory.Fibered.CartesianBasedFunctor.YonedaEvaluation.Slice
public import ReasLib.CategoryTheory.Fibered.Inertia.DiagonalComparison.RelativeDiagonal.Construction
public import ReasLib.CategoryTheory.Fibered.PseudoPullback.Pair
public import ReasLib.CategoryTheory.Fibered.Setoids.Bicategory
public import Mathlib.Tactic.CrossRefAttribute

/-!
# The isomorphism two-fibre product

For two objects `x y : X.p.Fiber U`, the source two-fibre product of Stacks Project,
Lemma 8.2.5 is the based pseudo-pullback of the relative diagonal by the pair of Yoneda maps. Its
second projection lands in `Over U`. This file also exposes the equivalent discrete Grothendieck
model of `Isom(x, y)`, which is the computationally useful canonical representative.

An ordinary categorical pullback of total categories would also admit isomorphisms covering
nonidentity base isomorphisms. The nested based pseudo-pullback below instead records the common
base and hence models the source's vertical comparison isomorphisms.
-/

@[expose] public section

universe u v

namespace CategoryTheory

open Opposite

variable {C : Type u} [Category.{v} C]

namespace FiberedCategoryOver.TwoFibreProduct.Isomorphism

variable (X : FiberedCategoryOver C) {U : C} (x y : X.p.Fiber U)

/-- The slice fibration `C/U` regarded as a based category over `C`. -/
abbrev slice (U : C) : BasedCategory C :=
  (FiberedCategoryOver.ofFunctor (Over.forget U)).toBasedCategory

/-- The cartesian Yoneda map associated to a fibre object. This is the neutral owner; it retains
the preservation of strongly cartesian arrows before passing to the based-functor interface used
by the pseudo-pullback construction. -/
@[stacks 04SI "cartesian Yoneda map for the isomorphism fibre"]
noncomputable def yonedaCartesianMap {U : C} (z : X.p.Fiber U) :
    CartesianBasedFunctor (Over.forget U) X.p :=
  (CartesianBasedFunctor.Yoneda.Chosen.functor X.p U).obj z

/-- The underlying based Yoneda map associated to a fibre object. -/
@[stacks 04SI "based Yoneda map for the isomorphism fibre"]
noncomputable abbrev yonedaMap {U : C} (z : X.p.Fiber U) :
    slice U ⥤ᵇ X.toBasedCategory :=
  (yonedaCartesianMap X z).toBasedFunctor

namespace yonedaCartesianMap

/-- Forgetting cartesian preservation from the neutral Yoneda map gives the based Yoneda map. -/
@[simp, stacks 04SI "Yoneda map forgetful bridge"]
theorem toBasedFunctor {U : C} (z : X.p.Fiber U) :
    (yonedaCartesianMap X z).toBasedFunctor = yonedaMap X z := sorry

end yonedaCartesianMap

/-- The relative product `X ×_C X`, represented as the self-pseudo-pullback of `X.toBase`. -/
@[stacks 04SI "relative product of the base fibration"]
abbrev relativeProduct : BasedCategory C :=
  BasedCategory.PseudoPullback X.toBasedCategory.toBase X.toBasedCategory.toBase

/-- The relative diagonal `X ⟶ X ×_C X`. -/
@[stacks 04SI "relative diagonal of the base fibration"]
def diagonal : X.toBasedCategory ⥤ᵇ relativeProduct X :=
  BasedFunctor.relativeDiagonal X.toBasedCategory.toBase

/-- The pair of based Yoneda maps `C/U ⟶ X ×_C X` associated to `x` and `y`. -/
@[stacks 04SI "paired Yoneda map"]
noncomputable def yonedaPair : slice U ⥤ᵇ relativeProduct X :=
  BasedCategory.PseudoPullback.pair (yonedaMap X x) (yonedaMap X y)

/-- The source two-fibre product `X ×_{X ×_C X, (x,y)} C/U` of Lemma 8.2.5. -/
@[stacks 04SI "isomorphism two-fibre-product source"]
noncomputable def source : BasedCategory C :=
  BasedCategory.PseudoPullback (diagonal X) (yonedaPair X x y)

/-- The based second projection from the source two-fibre product to `C/U`. -/
@[stacks 04SI "based source projection"]
noncomputable def sourceProjectionBased : source X x y ⥤ᵇ slice U :=
  BasedCategory.PseudoPullback.snd (diagonal X) (yonedaPair X x y)

/-- The projection from the source two-fibre product to the slice category `C/U`. -/
@[stacks 04SI "source projection to the slice"]
noncomputable abbrev sourceProjection : (source X x y).obj ⥤ Over U :=
  (sourceProjectionBased X x y).toFunctor

/-- The source two-fibre-product owner, retaining the native total-category instance.

`BasedCategory.ofFunctor` is intentionally convenient for arbitrary functors, but it reconstructs
the category on the total type from typeclass inference.  The nested pseudo-pullback already owns
the relevant category instance, so this owner preserves that instance for equivalence and fibre
constructions downstream. -/
@[stacks 04SI "native source owner over the slice"]
noncomputable abbrev sourceBased : BasedCategory (Over U) where
  obj := (source X x y).obj
  category := (source X x y).category
  p := sourceProjection X x y

/-- Lemma 8.2.5 (1): the source two-fibre product is fibred in setoids over `C/U`. -/
@[stacks 04SI "(1)"]
instance sourceProjectionInSetoids :
    Functor.IsFibered.InSetoids (sourceProjection X x y) := sorry

/-- The setoid-fibred source projection is, in particular, fibred. -/
@[stacks 04SI "source projection fibredness"]
instance sourceProjectionIsFibered :
    (sourceProjection X x y).IsFibered :=
  Functor.IsFibered.InGroupoids.toIsFibered

/-- The source based owner is fibred over `C/U` with its native category instance. -/
@[stacks 04SI "native source owner fibredness"]
instance sourceBasedIsFibered : (sourceBased X x y).p.IsFibered :=
  sourceProjectionIsFibered X x y

/-- The literal two-fibre-product source bundled at its natural setoid-fibred owner. This keeps
the native total-category instance of `sourceBased` while making the full setoid API available
without rebuilding a full-subcategory object at each use site. -/
@[stacks 04SI "(1) setoid-fibred source owner"]
noncomputable def sourceSetoids : FiberedCategoryOver.Setoids (Over U) :=
  ⟨sourceBased X x y, sourceProjectionInSetoids X x y⟩

namespace sourceSetoids

/-- Forgetting the setoid-fibred owner recovers the native based source. -/
@[simp]
theorem toBasedCategory :
    (sourceSetoids X x y).toBasedCategory = sourceBased X x y := sorry

/-- The projection of the bundled setoid-fibred source is the literal source projection. -/
@[simp]
theorem p :
    (sourceSetoids X x y).p = sourceProjection X x y := sorry

end sourceSetoids

/-- The canonical isomorphism-section presheaf associated to `x` and `y`. -/
@[stacks 04SI "isomorphism section presheaf"]
noncomputable abbrev presheaf : Functor (Over U)ᵒᵖ (Type _) :=
  Functor.isomorphismPresheaf X.p x y

/-- The size-stable lift of the canonical isomorphism-section presheaf.

The lift normalizes section values to the universe of the slice base, so the associated
category-of-elements uses the corresponding canonical total-category universe. -/
@[stacks 04SI "lifted isomorphism section presheaf"]
noncomputable abbrev presheafULift : Functor (Over U)ᵒᵖ (Type _) :=
  Functor.isomorphismPresheafULift X.p x y

/-- The discrete Grothendieck construction of `Isom(x, y)`, used as the canonical discrete
representative of the source two-fibre product over `Over U`. -/
@[stacks 04SI "isomorphism Grothendieck representative"]
noncomputable abbrev fibration : FiberedCategoryOver.Sets (Over U) :=
  Functor.isomorphismGrothendieckULift X.p x y

/-- The total category of the canonical discrete representative of the isomorphism two-fibre
product. -/
@[stacks 04SI "isomorphism representative total category"]
noncomputable abbrev total := (fibration X x y).total

/-- The projection of the canonical discrete representative to `Over U`. -/
@[stacks 04SI "isomorphism representative projection"]
noncomputable abbrev projection : Functor (total X x y) (Over U) :=
  (fibration X x y).p

/-- The canonical discrete representative is fibred in setoids over `Over U`. -/
@[stacks 04SI "isomorphism representative setoid fibredness"]
instance projectionInSetoids :
    Functor.IsFibered.InSetoids (projection X x y) := sorry

namespace presheafULift

/-- Straightening the canonical discrete representative recovers its defining isomorphism
presheaf. This bridge is the generic Grothendieck comparison specialized to `Isom(x, y)`. -/
@[stacks 04SI "representative fiber-object presheaf comparison"]
noncomputable def fiberObjectIso :
    presheafULift X x y ≅ (projection X x y).fiberObjectPresheaf :=
  (Functor.isomorphismGrothendieckULift.presheafIso X.p x y).symm
/- Data audit: `toPresheaf` stores `fiberObjectPresheaf` as its object map, so the displayed target
is definitionally the endpoint of the generic Grothendieck comparison. No equality transport is
part of this isomorphism's morphism data. -/

namespace fiberObjectIso.hom

/-- Pointwise, straightening sends an isomorphism-presheaf section to its tautological object in
the corresponding Grothendieck fibre. -/
@[simp]
theorem app (A : (Over U)ᵒᵖ) (s : (presheafULift X x y).obj A) :
    (fiberObjectIso X x y).hom.app A s =
      FiberedCategoryOver.Sets.ofPresheaf.valueToFiber
        (presheafULift X x y) (unop A) s := sorry

end fiberObjectIso.hom

namespace fiberObjectIso.inv

/-- Pointwise, unstraightening reads the value stored by an object of the corresponding
Grothendieck fibre. -/
@[simp]
theorem app (A : (Over U)ᵒᵖ) (q : (projection X x y).Fiber (unop A)) :
    (fiberObjectIso X x y).inv.app A q =
      FiberedCategoryOver.Sets.ofPresheaf.fiberToValue
        (presheafULift X x y) (unop A) q := sorry

end fiberObjectIso.inv

end presheafULift

/-- The canonical discrete representative bridge identifies `Isom(x, y)` with the presheaf of
fibrewise isomorphism classes of that representative. The literal-source comparison is
`collapse.sourcePresheafIso`. -/
@[stacks 04SI "source-to-representative presheaf comparison"]
noncomputable def presheafIso :
    presheafULift X x y ≅
      Functor.fiberIsoClassPresheaf (projection X x y) :=
  (Functor.isomorphismGrothendieckULift.isoClassPresheafIso X.p x y).symm

namespace presheafIso.hom

/-- Pointwise, the canonical comparison sends a section to the isomorphism class of its
tautological object in the corresponding Grothendieck fibre. -/
@[simp]
theorem app (A : (Over U)ᵒᵖ) (s : (presheafULift X x y).obj A) :
    (presheafIso X x y).hom.app A s =
      Quotient.mk''
        (FiberedCategoryOver.Sets.ofPresheaf.valueToFiber
          (presheafULift X x y) (unop A) s) := sorry

end presheafIso.hom

namespace presheafIso.inv

/-- Pointwise, the inverse canonical comparison reads the value represented by an object in the
corresponding Grothendieck fibre. -/
@[simp]
theorem app_mk (A : (Over U)ᵒᵖ)
    (q : (projection X x y).Fiber (unop A)) :
    (presheafIso X x y).inv.app A (Quotient.mk'' q) =
      FiberedCategoryOver.Sets.ofPresheaf.fiberToValue
        (presheafULift X x y) (unop A) q := sorry

end presheafIso.inv

end FiberedCategoryOver.TwoFibreProduct.Isomorphism

end CategoryTheory
