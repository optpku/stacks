module

public import stacks_project.Chap94.Definition_94_16_5_Quotient
public import stacks_project.Chap94.Lemma_94_16_1_KernelPair
public import ReasLib.CategoryTheory.Fibered.PseudoPullback.Basic.Construction

/-!
# Recovering an arrow from the kernel pair of a quotient atlas

The prestack of a groupoid in algebraic spaces has sheaves of morphisms. Its
stackification is therefore fully faithful. We lift the inverse of the kernel-pair
comparison through that actual functor and extract its underlying `R`-point.
The first kernel-pair projection is the target and the second is the source.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open FiberedCategoryOver.Groupoids Opposite BasedNatIso
open AlgebraicGeometry.AlgebraicStack BasedCategory.PseudoPullback
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidAlgebraicSpace

variable {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B)

/-- Stackification of the groupoid prestack is bijective on each total-category Hom set:
its morphism presheaves are sheaves because `R` is an algebraic space. -/
theorem stackificationHom_map_bijective (a b : G.preQuotient.total) :
    Function.Bijective
      ((toFunctor G.stackificationHom).map : (a ⟶ b) →
        ((toFunctor G.stackificationHom).obj a ⟶
          (toFunctor G.stackificationHom).obj b)) := sorry

/-- The Hom equivalence of the actual stackification functor, with its specified forward map. -/
def stackificationHomEquiv (a b : G.preQuotient.total) :
    (a ⟶ b) ≃ ((toFunctor G.stackificationHom).obj a ⟶
      (toFunctor G.stackificationHom).obj b) :=
  Equiv.ofBijective _ (G.stackificationHom_map_bijective a b)

/-- Lifting and then applying stackification returns the supplied morphism. -/
theorem stackificationHomEquiv_symm_spec {a b : G.preQuotient.total}
    (f : (toFunctor G.stackificationHom).obj a ⟶
      (toFunctor G.stackificationHom).obj b) :
    (toFunctor G.stackificationHom).map ((G.stackificationHomEquiv a b).symm f) = f :=
  Equiv.apply_symm_apply (G.stackificationHomEquiv a b) f

/-- The uniquely determined prestack arrow from the second point to the first point of the
kernel pair. Its stacked image is the inverse of the stored comparison isomorphism. -/
def quotientKernelPreArrow (x : (kernelPair G.atlas).total) :
    G.atlasToPreQuotientFunctor.obj (sndObj x) ⟶
      G.atlasToPreQuotientFunctor.obj (fstObj x) :=
  (G.stackificationHomEquiv _ _).symm (comparisonIsoApp x).inv

/-- The recovered prestack arrow has exactly the original kernel-pair comparison as image. -/
theorem quotientKernelPreArrow_spec (x : (kernelPair G.atlas).total) :
    (toFunctor G.stackificationHom).map (G.quotientKernelPreArrow x) =
      (comparisonIsoApp x).inv :=
  G.stackificationHomEquiv_symm_spec _

/-- The recovered arrow is independent of any inverse-choice implementation. -/
theorem quotientKernelPreArrow_unique (x : (kernelPair G.atlas).total)
    (f : G.atlasToPreQuotientFunctor.obj (sndObj x) ⟶
      G.atlasToPreQuotientFunctor.obj (fstObj x))
    (hf : (toFunctor G.stackificationHom).map f = (comparisonIsoApp x).inv) :
    f = G.quotientKernelPreArrow x := sorry

/-- The `R`-point extracted from the lifted prestack arrow, over the second point's base. -/
def quotientKernelArrowObj (x : (kernelPair G.atlas).total) : G.R.left.toGroupoids.total :=
  op ⟨(sndObj x).unop.fst, (G.quotientKernelPreArrow x).fiber.arrow⟩

/-- A morphism of kernel-pair points restricts the recovered arrow along its second base map. -/
def quotientKernelArrowMap {x y : (kernelPair G.atlas).total} (f : x ⟶ y) :
    G.quotientKernelArrowObj x ⟶ G.quotientKernelArrowObj y :=
  Quiver.Hom.op ⟨(sndMap f).unop.val, sorry⟩

/-- Arrow recovery as a functor of total categories. Both its objects and maps are explicit. -/
def quotientKernelArrowFunctor : (kernelPair G.atlas).total ⥤ G.R.left.toGroupoids.total where
  obj := G.quotientKernelArrowObj
  map := G.quotientKernelArrowMap
  map_id := sorry
  map_comp := sorry

/-- The reverse comparison `U ×_[U/R] U ⟶ R`, obtained by lifting and extracting arrows. -/
def quotientKernelToArrow : kernelPair G.atlas ⟶ G.R.left.toGroupoids :=
  ofBasedFunctor { toFunctor := G.quotientKernelArrowFunctor, w := sorry }

/-- The source of the extracted arrow is the second kernel-pair point, over the identity. -/
def quotientKernelToArrowSourceApp (x : (kernelPair G.atlas).total) :
    (toFunctor (G.quotientKernelToArrow ≫ toGroupoids.map G.s.left)).obj x ≅
      (toFunctor (pr1 G.atlas)).obj x where
  hom := Quiver.Hom.op ⟨𝟙 _, sorry⟩
  inv := Quiver.Hom.op ⟨𝟙 _, sorry⟩
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The target of the extracted arrow is the first point, transported by the two stored base
equalities of the kernel pair. These are equalities of bases, not of representing spaces. -/
def quotientKernelToArrowTargetApp (x : (kernelPair G.atlas).total) :
    (toFunctor (G.quotientKernelToArrow ≫ toGroupoids.map G.t.left)).obj x ≅
      (toFunctor (pr0 G.atlas)).obj x where
  hom := Quiver.Hom.op
    ⟨((sndBaseIso x ≪≫ (fstBaseIso x).symm).hom).op, sorry⟩
  inv := Quiver.Hom.op
    ⟨((sndBaseIso x ≪≫ (fstBaseIso x).symm).inv).op, sorry⟩
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The reverse comparison preserves the second projection as the actual source map. -/
def quotientKernelToArrow_sourceIso :
    G.quotientKernelToArrow ≫ toGroupoids.map G.s.left ≅ pr1 G.atlas :=
  BasedFunctorIso.lift
    (ofComponents (G.quotientKernelToArrowSourceApp) (fun {_ _} _ ↦ sorry) (fun _ ↦ sorry))

/-- The reverse comparison preserves the first projection as the actual target map. -/
def quotientKernelToArrow_targetIso :
    G.quotientKernelToArrow ≫ toGroupoids.map G.t.left ≅ pr0 G.atlas :=
  BasedFunctorIso.lift
    (ofComponents (G.quotientKernelToArrowTargetApp) (fun {_ _} _ ↦ sorry) (fun _ ↦ sorry))

end AlgebraicGeometry.GroupoidAlgebraicSpace
