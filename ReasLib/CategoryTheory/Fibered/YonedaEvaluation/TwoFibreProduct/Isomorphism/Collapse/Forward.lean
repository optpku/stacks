/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.YonedaEvaluation.TwoFibreProduct.Isomorphism
public import ReasLib.CategoryTheory.Fibered.CategoryOver.HomPresheaf
public import ReasLib.CategoryTheory.Fibered.BasedCategory.CategoryOfElements
public import ReasLib.CategoryTheory.Fibered.BasedCategory.NaturalIso
public import ReasLib.CategoryTheory.Fibered.PseudoPullback.Iso
public import ReasLib.CategoryTheory.Fibered.BasedCategory.Equivalence.Bicategorical

/-!
# Collapsing the literal isomorphism two-fibre product: forward data

This leaf constructs the collapsed isomorphism section and the resulting functor into the
discrete Grothendieck construction.
-/

@[expose] public section

/- The public owners below expose the semantic object, map, and component data.  Only proof-valued
functoriality, verticality, and coherence obligations remain implementation details. -/
universe u v

namespace CategoryTheory

open Opposite CategoryOfElements
open scoped Bicategory BasedFunctor

variable {C : Type u} [Category.{v} C]

namespace FiberedCategoryOver.TwoFibreProduct.Isomorphism

variable (X : FiberedCategoryOver C) {U : C} (x y : X.p.Fiber U)

namespace collapse

namespace isomSection

/-- The slice object carried by a literal two-fibre-product object. -/
@[stacks 04SI "collapse slice-object readout"]
noncomputable abbrev slice (Q : (source X x y).obj) : Over U :=
  BasedCategory.PseudoPullback.sndObj Q

/-- The intermediate total-category object carried by a literal two-fibre-product object. -/
@[stacks 04SI "collapse middle-object readout"]
noncomputable abbrev middle (Q : (source X x y).obj) : X.total :=
  BasedCategory.PseudoPullback.fstObj Q

/-- The outer pseudo-pullback comparison carried by a literal object. -/
@[stacks 04SI "collapse outer comparison"]
noncomputable def outerIso (Q : (source X x y).obj) :
    (diagonal X).obj (middle X x y Q) ≅
      (yonedaPair X x y).obj (slice X x y Q) :=
  BasedCategory.PseudoPullback.comparisonIsoApp Q

/-- The first projected comparison with the left Yoneda section. -/
@[stacks 04SI "collapse left comparison"]
noncomputable def leftIso (Q : (source X x y).obj) :
    middle X x y Q ≅ (yonedaMap X x).obj (slice X x y Q) :=
  (BasedCategory.PseudoPullback.fst X.toBasedCategory.toBase
    X.toBasedCategory.toBase).toFunctor.mapIso (outerIso X x y Q)

/-- The second projected comparison with the right Yoneda section. -/
@[stacks 04SI "collapse right comparison"]
noncomputable def rightIso (Q : (source X x y).obj) :
    middle X x y Q ≅ (yonedaMap X y).obj (slice X x y Q) :=
  (BasedCategory.PseudoPullback.snd X.toBasedCategory.toBase
    X.toBasedCategory.toBase).toFunctor.mapIso (outerIso X x y Q)
/- Data audit: the projection functors store `fstObj` and `sndObj` as their object maps. Hence
both endpoint identifications reduce definitionally, and the two comparisons contain only the
projected morphism data of `outerIso`. -/

/-- The forward left comparison is a morphism in the fibre over the source of the displayed
slice object. -/
@[stacks 04SI "collapse left comparison verticality"]
theorem leftIso.hom.isHomLift (Q : (source X x y).obj) :
    X.p.IsHomLift (𝟙 (slice X x y Q).left) (leftIso X x y Q).hom := sorry

/-- The inverse left comparison is a morphism in the fibre over the source of the displayed
slice object. -/
@[stacks 04SI "collapse inverse-left verticality"]
theorem leftIso.inv.isHomLift (Q : (source X x y).obj) :
    X.p.IsHomLift (𝟙 (slice X x y Q).left) (leftIso X x y Q).inv := sorry

/-- The forward right comparison is a morphism in the fibre over the source of the displayed
slice object. -/
@[stacks 04SI "collapse right comparison verticality"]
theorem rightIso.hom.isHomLift (Q : (source X x y).obj) :
    X.p.IsHomLift (𝟙 (slice X x y Q).left) (rightIso X x y Q).hom := sorry

/-- The inverse right comparison is a morphism in the fibre over the source of the displayed
slice object. -/
@[stacks 04SI "collapse inverse-right verticality"]
theorem rightIso.inv.isHomLift (Q : (source X x y).obj) :
    X.p.IsHomLift (𝟙 (slice X x y Q).left) (rightIso X x y Q).inv := sorry

/-- The isomorphism between the two selected reindexings obtained by collapsing the literal
triple `(z, α, β)`. -/
@[stacks 04SI "collapse selected comparison"]
noncomputable def chosenIso (Q : (source X x y).obj) :
    ((Functor.Chosen.reindex X.p (slice X x y Q).hom).obj x).1 ≅
      ((Functor.Chosen.reindex X.p (slice X x y Q).hom).obj y).1 :=
  (Functor.Fiber.fiberInclusion : X.p.Fiber (slice X x y Q).left ⥤ X.total).mapIso
      (CartesianBasedFunctor.Yoneda.Slice.Chosen.sectionIso X.p x
        (slice X x y Q)).symm ≪≫
  (leftIso X x y Q).symm ≪≫ rightIso X x y Q ≪≫
  (Functor.Fiber.fiberInclusion : X.p.Fiber (slice X x y Q).left ⥤ X.total).mapIso
      (CartesianBasedFunctor.Yoneda.Slice.Chosen.sectionIso X.p y
        (slice X x y Q))

/-- The collapsed chosen comparison is `α⁻¹ ≫ β`, up to the canonical Yoneda-section
endpoint comparisons. -/
@[simp, stacks 04SI "collapse selected comparison readout"]
theorem chosenIso.hom (Q : (source X x y).obj) :
    (chosenIso X x y Q).hom =
      ((Functor.Fiber.fiberInclusion :
          X.p.Fiber (slice X x y Q).left ⥤ X.total).mapIso
        (CartesianBasedFunctor.Yoneda.Slice.Chosen.sectionIso
          X.p x (slice X x y Q)).symm).hom ≫
      (leftIso X x y Q).inv ≫
      (rightIso X x y Q).hom ≫
      ((Functor.Fiber.fiberInclusion :
          X.p.Fiber (slice X x y Q).left ⥤ X.total).mapIso
        (CartesianBasedFunctor.Yoneda.Slice.Chosen.sectionIso
          X.p y (slice X x y Q))).hom := sorry

/-- The collapsed chosen-reindexing comparison is vertical over the identity of the slice
domain. -/
@[stacks 04SI "collapse selected comparison verticality"]
theorem chosenIso.isHomLift (Q : (source X x y).obj) :
    X.p.IsHomLift (𝟙 (slice X x y Q).left) (chosenIso X x y Q).hom := sorry

/-- The collapsed comparison transported from the chosen reindexing to the raw
`fiberPseudofunctor` reindexing used by `isomorphismPresheaf`. -/
@[stacks 04SI "collapse fiber comparison"]
noncomputable def fiberIso (Q : (source X x y).obj) :
    ((X.p.fiberPseudofunctor.map (slice X x y Q).hom.op.toLoc).toFunctor.obj x) ≅
      ((X.p.fiberPseudofunctor.map (slice X x y Q).hom.op.toLoc).toFunctor.obj y) :=
  (Functor.FiberPseudofunctor.mapIso X.p (slice X x y Q).hom).app x ≪≫
    Functor.Fiber.isoMk (chosenIso X x y Q)
      (hhom := chosenIso.isHomLift X x y Q) ≪≫
    ((Functor.FiberPseudofunctor.mapIso X.p (slice X x y Q).hom).app y).symm

end isomSection

/-- The isomorphism-presheaf section carried by a literal two-fibre-product object. -/
@[stacks 04SI "collapse isomorphism section"]
noncomputable def isomSection (Q : (source X x y).obj) :
    (presheaf X x y).obj (op (isomSection.slice X x y Q)) :=
  Pseudofunctor.IsomSubpresheaf.mk (Functor.fiberPseudofunctor X.p) x y
    (isomSection.fiberIso X x y Q).hom

namespace isomSection

/-- The collapsed section is natural along morphisms in the literal source. -/
@[simp, stacks 04SI "collapse section naturality"]
theorem naturality {Q R : (source X x y).obj} (f : Q ⟶ R) :
    (presheaf X x y).map ((sourceProjection X x y).map f).op (isomSection X x y R) =
      isomSection X x y Q := sorry

/-- The lifted collapsed section used by the size-stable Grothendieck owner. -/
@[stacks 04SI "lifted collapse section"]
noncomputable abbrev ulift (Q : (source X x y).obj) :
    (presheafULift X x y).obj (op (slice X x y Q)) :=
  ULift.up (collapse.isomSection X x y Q)

/-- Naturality of the lifted collapsed section. -/
@[simp, stacks 04SI "lifted collapse section naturality"]
theorem ulift.naturality {Q R : (source X x y).obj} (f : Q ⟶ R) :
    (presheafULift X x y).map
        ((sourceProjection X x y).map f).op (ulift X x y R) =
      ulift X x y Q := sorry

/-- Naturality in the opposite source category, in the exact form required to package the lifted
collapsed values as a section. -/
@[stacks 04SI "lifted collapse section property"]
theorem uliftSection_property {Q R : (sourceBased X x y).objᵒᵖ} (f : Q ⟶ R) :
    ((sourceBased X x y).p.op ⋙ presheafULift X x y).map f
        (ulift X x y Q.unop) =
      ulift X x y R.unop := sorry

/-- The lifted collapsed values as a section of the isomorphism presheaf pulled back to the
literal source.  This is the complete datum from which the collapse functor is generated. -/
@[stacks 04SI "collapse lifted section owner"]
noncomputable def uliftSection :
    ((sourceBased X x y).p.op ⋙ presheafULift X x y).sections :=
  ⟨fun Q => ulift X x y Q.unop, fun f => uliftSection_property X x y f⟩

end isomSection

/-- The Grothendieck element associated to the collapsed isomorphism section. -/
@[stacks 04SI "collapse Grothendieck element"]
noncomputable abbrev element (Q : (source X x y).obj) :
    (presheafULift X x y).Elements :=
  CategoryOfElements.Section.element (sourceBased X x y).p
    (presheafULift X x y) (isomSection.uliftSection X x y) Q

end collapse

end FiberedCategoryOver.TwoFibreProduct.Isomorphism
end CategoryTheory
