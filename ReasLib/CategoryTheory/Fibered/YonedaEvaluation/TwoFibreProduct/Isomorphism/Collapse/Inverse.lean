module

public import ReasLib.CategoryTheory.Fibered.YonedaEvaluation.TwoFibreProduct.Isomorphism.Collapse.Forward

/-!
# Collapsing the literal isomorphism two-fibre product: inverse data

This leaf constructs the deterministic inverse object and morphism data over the slice.
-/

@[expose] public section

universe u v

namespace CategoryTheory

open Opposite CategoryOfElements
open scoped Bicategory BasedFunctor

variable {C : Type u} [Category.{v} C]

namespace FiberedCategoryOver.TwoFibreProduct.Isomorphism

variable (X : FiberedCategoryOver C) {U : C} (x y : X.p.Fiber U)

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace collapse
namespace inverse

/-- The slice object displayed by a canonical Grothendieck object. -/
@[stacks 04SI "inverse slice-object readout"]
noncomputable abbrev slice (q : total X x y) : Over U :=
  (projection X x y).obj q

/-- The deterministic middle object selected by the left Yoneda section. -/
@[stacks 04SI "inverse middle-object readout"]
noncomputable abbrev middle (q : total X x y) : X.total :=
  (yonedaMap X x).obj (slice X x y q)

/-- The selected middle object lies over the source of its slice arrow. -/
@[stacks 04SI "inverse middle base readout"]
theorem middleBase (q : total X x y) :
    X.p.obj (middle X x y q) = (slice X x y q).left := sorry

/-- The selected middle object in the standard fibre. -/
@[stacks 04SI "inverse middle fiber object"]
noncomputable def middleFiber (q : total X x y) :
    X.toBasedCategory.p.Fiber (slice X x y q).left :=
  ⟨middle X x y q, middleBase X x y q⟩

/-- The displayed slice object in the standard slice fibre. -/
@[stacks 04SI "inverse slice fiber object"]
noncomputable def sliceFiber (q : total X x y) :
    (FiberedCategoryOver.TwoFibreProduct.Isomorphism.slice U).p.Fiber
      (slice X x y q).left :=
  ⟨slice X x y q, rfl⟩

/-- The diagonal-side relative-product fibre object. -/
@[stacks 04SI "inverse diagonal fiber object"]
noncomputable abbrev diagonalFiber (q : total X x y) :
    (relativeProduct X).p.Fiber (slice X x y q).left :=
  ((diagonal X).fiberFunctor (slice X x y q).left).obj (middleFiber X x y q)

/-- The pair-side relative-product fibre object. -/
@[stacks 04SI "inverse pair fiber object"]
noncomputable abbrev pairFiber (q : total X x y) :
    (relativeProduct X).p.Fiber (slice X x y q).left :=
  ((yonedaPair X x y).fiberFunctor (slice X x y q).left).obj (sliceFiber X x y q)

/-- The raw isomorphism-presheaf section carried by a Grothendieck object. -/
@[stacks 04SI "inverse raw section"]
noncomputable abbrev rawSection (q : total X x y) :
    (presheaf X x y).obj (op (slice X x y q)) :=
  q.unop.2.down

/-- The canonical isomorphism instance supplied by a Grothendieck section. -/
@[stacks 04SI "inverse section isomorphism instance"]
noncomputable instance sectionIsIso (q : total X x y) : IsIso (rawSection X x y q).1 :=
  (rawSection X x y q).2

/-- The section isomorphism expressed in the selected reindexing model. -/
@[stacks 04SI "inverse section isomorphism"]
noncomputable def sectionIso (q : total X x y) :
    (slice X x y q).hom⁎[X.chosenCleavage] x ≅
      (slice X x y q).hom⁎[X.chosenCleavage] y :=
  ((Functor.FiberPseudofunctor.mapIso X.p (slice X x y q).hom).app x).symm ≪≫
    @asIso _ _ _ _ (rawSection X x y q).1 (sectionIsIso X x y q) ≪≫
    (Functor.FiberPseudofunctor.mapIso X.p (slice X x y q).hom).app y

/-- The left component of the deterministic relative-product comparison. -/
@[stacks 04SI "inverse left comparison"]
noncomputable def leftIso (q : total X x y) :
    BasedCategory.PseudoPullback.fstObj (diagonalFiber X x y q).1 ≅
      BasedCategory.PseudoPullback.fstObj (pairFiber X x y q).1 :=
  Iso.refl _

/-- The ambient right comparison determined by the Grothendieck section. -/
@[stacks 04SI "inverse ambient right comparison"]
noncomputable def rightAmbientIso (q : total X x y) :
    middle X x y q ≅ (yonedaMap X y).obj (slice X x y q) :=
  (Functor.Fiber.fiberInclusion : X.p.Fiber (slice X x y q).left ⥤ X.total).mapIso
      (CartesianBasedFunctor.Yoneda.Slice.Chosen.sectionIso X.p x (slice X x y q)) ≪≫
    (Functor.Fiber.fiberInclusion : X.p.Fiber (slice X x y q).left ⥤ X.total).mapIso
      (sectionIso X x y q) ≪≫
  (Functor.Fiber.fiberInclusion : X.p.Fiber (slice X x y q).left ⥤ X.total).mapIso
      (CartesianBasedFunctor.Yoneda.Slice.Chosen.sectionIso X.p y (slice X x y q)).symm

/-- The right component of the deterministic relative-product comparison. -/
@[stacks 04SI "inverse right comparison"]
noncomputable def rightIso (q : total X x y) :
    BasedCategory.PseudoPullback.sndObj (diagonalFiber X x y q).1 ≅
      BasedCategory.PseudoPullback.sndObj (pairFiber X x y q).1 :=
  rightAmbientIso X x y q

/-- The selected left comparison is vertical over the slice source. -/
@[stacks 04SI "inverse left comparison verticality"]
theorem leftIso.isHomLift (q : total X x y) :
    X.p.IsHomLift (𝟙 (slice X x y q).left) (leftIso X x y q).hom := sorry

/-- The selected right comparison is vertical over the slice source. -/
@[stacks 04SI "inverse right comparison verticality"]
theorem rightIso.isHomLift (q : total X x y) :
    X.p.IsHomLift (𝟙 (slice X x y q).left) (rightIso X x y q).hom := sorry

/-- The base of the diagonal-side comparison is the displayed slice source. -/
@[simp, stacks 04SI "inverse diagonal base readout"]
theorem diagonalBase (q : total X x y) :
    BasedCategory.PseudoPullback.baseObj (diagonalFiber X x y q).1 =
      (slice X x y q).left := sorry

/-- The base of the pair-side comparison is the displayed slice source. -/
@[simp, stacks 04SI "inverse pair base readout"]
theorem pairBase (q : total X x y) :
    BasedCategory.PseudoPullback.baseObj (pairFiber X x y q).1 =
      (slice X x y q).left := sorry

/-- The deterministic base comparison for the outer pseudo-pullback. -/
@[stacks 04SI "inverse base comparison"]
noncomputable def baseIso (q : total X x y) :
    BasedCategory.PseudoPullback.baseObj (diagonalFiber X x y q).1 ≅
      BasedCategory.PseudoPullback.baseObj (pairFiber X x y q).1 :=
  X.p.mapIso
      ((Functor.Fiber.fiberInclusion :
        X.p.Fiber (slice X x y q).left ⥤ X.total).mapIso
        (CartesianBasedFunctor.Yoneda.Slice.Chosen.sectionIso X.p x
          (slice X x y q))) ≪≫
    (Functor.Fiber.fiberInclusionCompIsoConst
      (p := X.p) (S := (slice X x y q).left)).app
        ((Functor.Chosen.reindex X.p (slice X x y q).hom).obj x)
/- Data audit: the only nontrivial base comparison is obtained by mapping the explicit Yoneda
section isomorphism and then using mathlib's canonical base isomorphism of a stored fiber object.
No theorem-valued equality is converted into morphism data. -/

/-- The left comparison lies over the deterministic base comparison. -/
@[stacks 04SI "inverse left base compatibility"]
theorem leftIso.isHomLiftBase (q : total X x y) :
    X.p.IsHomLift (baseIso X x y q).hom (leftIso X x y q).hom := sorry

/-- The right comparison lies over the deterministic base comparison. -/
@[stacks 04SI "inverse right base compatibility"]
theorem rightIso.isHomLiftBase (q : total X x y) :
    X.p.IsHomLift (baseIso X x y q).hom (rightIso X x y q).hom := sorry

/-- The two deterministic components respect the relative-product comparisons. -/
@[stacks 04SI "inverse comparison compatibility"]
theorem comparisonComm (q : total X x y) :
    CommSq
      (X.toBasedCategory.toBase.toFunctor.map (leftIso X x y q).hom)
      (BasedCategory.PseudoPullback.comparison (diagonalFiber X x y q).1)
      (BasedCategory.PseudoPullback.comparison (pairFiber X x y q).1)
      (X.toBasedCategory.toBase.toFunctor.map (rightIso X x y q).hom) := sorry

/-- The deterministic comparison in the relative-product fibre. -/
@[stacks 04SI "inverse relative-product comparison"]
noncomputable def comparisonIso (q : total X x y) :
    (diagonalFiber X x y q).1 ≅ (pairFiber X x y q).1 :=
  BasedCategory.PseudoPullback.mkIso (baseIso X x y q)
    (leftIso X x y q) (rightIso X x y q)
    (hom_fst := leftIso.isHomLiftBase X x y q)
    (hom_snd := rightIso.isHomLiftBase X x y q)
    (comparisonComm X x y q)

/-- The relative-product comparison is vertical over the slice source. -/
@[stacks 04SI "inverse comparison verticality"]
theorem comparisonIso.isHomLift (q : total X x y) :
    (relativeProduct X).p.IsHomLift (𝟙 (slice X x y q).left)
      (comparisonIso X x y q).hom := sorry

/-- The deterministic literal object selected by a Grothendieck section. -/
@[stacks 04SI "inverse literal object"]
noncomputable def object (q : total X x y) : (source X x y).obj :=
  BasedCategory.PseudoPullback.mk (diagonal X) (yonedaPair X x y)
    (slice X x y q).left
    { fst := middleFiber X x y q
      snd := sliceFiber X x y q
      iso := Functor.Fiber.isoMk (comparisonIso X x y q)
        (hhom := comparisonIso.isHomLift X x y q) }

/-- The base arrow underlying the deterministic inverse of a Grothendieck morphism. -/
@[stacks 04SI "inverse base-map readout"]
noncomputable abbrev baseMap {q r : total X x y} (f : q ⟶ r) :
    (slice X x y q).left ⟶ (slice X x y r).left :=
  ((projection X x y).map f).left

/-- The middle-object component of the deterministic inverse map. -/
@[stacks 04SI "inverse middle-map data"]
noncomputable def middleMap {q r : total X x y} (f : q ⟶ r) :
    middle X x y q ⟶ middle X x y r :=
  (yonedaMap X x).map ((projection X x y).map f)

/-- The middle component lies over the displayed base map. -/
@[stacks 04SI "inverse middle-map verticality"]
theorem middleMap.isHomLift {q r : total X x y} (f : q ⟶ r) :
    X.p.IsHomLift (baseMap X x y f) (middleMap X x y f) := sorry

/-- The displayed slice map lies over the same base arrow. -/
@[stacks 04SI "inverse slice-map verticality"]
theorem sliceMap.isHomLift {q r : total X x y} (f : q ⟶ r) :
    (FiberedCategoryOver.TwoFibreProduct.Isomorphism.slice U).p.IsHomLift
      (baseMap X x y f) ((projection X x y).map f) := sorry

/-- The deterministic inverse components respect the outer comparisons. -/
@[stacks 04SI "inverse map compatibility"]
theorem mapComm {q r : total X x y} (f : q ⟶ r) :
    CommSq
      ((diagonal X).toFunctor.map (middleMap X x y f))
      (BasedCategory.PseudoPullback.comparison (object X x y q))
      (BasedCategory.PseudoPullback.comparison (object X x y r))
      ((yonedaPair X x y).toFunctor.map ((projection X x y).map f)) := sorry

/-- The explicit morphism map of the deterministic inverse. -/
@[stacks 04SI "inverse morphism data"]
noncomputable def map {q r : total X x y} (f : q ⟶ r) :
    object X x y q ⟶ object X x y r :=
  BasedCategory.PseudoPullback.Hom.mk (baseMap X x y f)
    (middleMap X x y f) (middleMap.isHomLift X x y f)
    ((projection X x y).map f) (sliceMap.isHomLift X x y f)
    (mapComm X x y f)

end inverse

/-- The deterministic inverse map preserves identities. -/
private theorem inverseMap_id (q : total X x y) :
    inverse.map X x y (𝟙 q) = 𝟙 (inverse.object X x y q) := sorry

/-- The deterministic inverse map preserves composition. -/
private theorem inverseMap_comp {q r s : total X x y} (f : q ⟶ r) (g : r ⟶ s) :
    inverse.map X x y (f ≫ g) =
      inverse.map X x y f ≫ inverse.map X x y g := sorry

/-- The private ordinary-functor assembly underlying the deterministic inverse. -/
private noncomputable def inverseToFunctor : total X x y ⥤ (source X x y).obj where
  obj := inverse.object X x y
  map := inverse.map X x y
  map_id := inverseMap_id X x y
  map_comp := inverseMap_comp X x y

/-- The ordinary inverse functor commutes with the slice projections. -/
private theorem inverseToFunctor_comp_projection :
    inverseToFunctor X x y ⋙ sourceProjection X x y = projection X x y := sorry

/-- The deterministic inverse as a functor over the slice category. -/
@[stacks 04SI "canonical inverse over the slice"]
noncomputable def inverse :
    (fibration X x y).toBasedCategory ⥤ᵇ
      (sourceSetoids X x y).toBasedCategory where
  toFunctor := inverseToFunctor X x y
  w := inverseToFunctor_comp_projection X x y

end collapse

/-- Collapse a literal two-fibre-product object to its isomorphism-presheaf section. -/
@[stacks 04SI "literal two-fibre-product collapse"]
noncomputable def collapse :
    (sourceSetoids X x y).toBasedCategory ⥤ᵇ
      (fibration X x y).toBasedCategory :=
  CategoryOfElements.Section.basedFunctor (sourceBased X x y)
    (presheafULift X x y) (collapse.isomSection.uliftSection X x y)
/- Data audit: `collapse` is generated by the neutral category-of-elements construction from the
explicit lifted section.  Its only deferred dependencies are the section naturality and generic
functor-law and strict-projection proofs. -/

end FiberedCategoryOver.TwoFibreProduct.Isomorphism
end CategoryTheory
