/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.Quotient.Small
public import ReasLib.CategoryTheory.Fibered.Groupoids.KernelPair.Operations
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
open BasedCategory.PseudoPullback
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidAlgebraicSpace.SmallQuotient

variable {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B)

/-- Stackification of the groupoid prestack is bijective on each total-category Hom set:
its morphism presheaves are sheaves because `R` is an algebraic space. -/
theorem stackificationHom_map_bijective (a b : (preQuotient G).total) :
    Function.Bijective
      ((toFunctor (stackificationHom G)).map : (a ⟶ b) →
        ((toFunctor (stackificationHom G)).obj a ⟶
          (toFunctor (stackificationHom G)).obj b)) := sorry

/-- The Hom equivalence of the actual stackification functor, with its specified forward map. -/
def stackificationHomEquiv (a b : (preQuotient G).total) :
    (a ⟶ b) ≃ ((toFunctor (stackificationHom G)).obj a ⟶
      (toFunctor (stackificationHom G)).obj b) :=
  Equiv.ofBijective _ ((stackificationHom_map_bijective G) a b)

/-- Lifting and then applying stackification returns the supplied morphism. -/
theorem stackificationHomEquiv_symm_spec {a b : (preQuotient G).total}
    (f : (toFunctor (stackificationHom G)).obj a ⟶
      (toFunctor (stackificationHom G)).obj b) :
    (toFunctor (stackificationHom G)).map ((stackificationHomEquiv G a b).symm f) = f :=
  Equiv.apply_symm_apply (stackificationHomEquiv G a b) f

/-- The uniquely determined prestack arrow from the second point to the first point of the
kernel pair. Its stacked image is the inverse of the stored comparison isomorphism. -/
def quotientKernelPreArrow (x : (KernelPair.kernelPair.{u + 1, u, u + 1} (atlas G)).total) :
    (atlasToPreQuotientFunctor G).obj (sndObj x) ⟶
      (atlasToPreQuotientFunctor G).obj (fstObj x) :=
  (stackificationHomEquiv G _ _).symm (comparisonIsoApp x).inv

/-- The recovered prestack arrow has exactly the original kernel-pair comparison as image. -/
theorem quotientKernelPreArrow_spec (x : (KernelPair.kernelPair.{u + 1, u, u + 1} (atlas G)).total) :
    (toFunctor (stackificationHom G)).map (quotientKernelPreArrow G x) =
      (comparisonIsoApp x).inv :=
  (stackificationHomEquiv_symm_spec G) _

/-- The recovered arrow is independent of any inverse-choice implementation. -/
theorem quotientKernelPreArrow_unique (x : (KernelPair.kernelPair.{u + 1, u, u + 1} (atlas G)).total)
    (f : (atlasToPreQuotientFunctor G).obj (sndObj x) ⟶
      (atlasToPreQuotientFunctor G).obj (fstObj x))
    (hf : (toFunctor (stackificationHom G)).map f = (comparisonIsoApp x).inv) :
    f = quotientKernelPreArrow G x := sorry

/-- The `R`-point extracted from the lifted prestack arrow, over the second point's base. -/
def quotientKernelArrowObj (x : (KernelPair.kernelPair.{u + 1, u, u + 1} (atlas G)).total) :
    G.R.left.toGroupoids.total :=
  op ⟨(sndObj x).unop.fst, (quotientKernelPreArrow G x).fiber.arrow⟩

/-- A morphism of kernel-pair points restricts the recovered arrow along its second base map. -/
def quotientKernelArrowMap {x y : (KernelPair.kernelPair.{u + 1, u, u + 1} (atlas G)).total} (f : x ⟶ y) :
    quotientKernelArrowObj G x ⟶ quotientKernelArrowObj G y :=
  Quiver.Hom.op ⟨(sndMap f).unop.val, sorry⟩

/-- Arrow recovery as a functor of total categories. Both its objects and maps are explicit. -/
def quotientKernelArrowFunctor : (KernelPair.kernelPair.{u + 1, u, u + 1} (atlas G)).total ⥤
    G.R.left.toGroupoids.total where
  obj := (quotientKernelArrowObj G)
  map := (quotientKernelArrowMap G)
  map_id := sorry
  map_comp := sorry

/-- The reverse comparison `U ×_[U/R] U ⟶ R`, obtained by lifting and extracting arrows. -/
def quotientKernelToArrow : KernelPair.kernelPair.{u + 1, u, u + 1} (atlas G) ⟶ G.R.left.toGroupoids :=
  ofBasedFunctor { toFunctor := (quotientKernelArrowFunctor G), w := sorry }

/-- The source of the extracted arrow is the second kernel-pair point, over the identity. -/
def quotientKernelToArrowSourceApp (x : (KernelPair.kernelPair.{u + 1, u, u + 1} (atlas G)).total) :
    (toFunctor (quotientKernelToArrow G ≫ toGroupoids.map G.s.left)).obj x ≅
      (toFunctor (KernelPair.pr1.{u + 1, u, u + 1} (atlas G))).obj x where
  hom := Quiver.Hom.op ⟨𝟙 _, sorry⟩
  inv := Quiver.Hom.op ⟨𝟙 _, sorry⟩
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The target of the extracted arrow is the first point, transported by the two stored base
equalities of the kernel pair. These are equalities of bases, not of representing spaces. -/
def quotientKernelToArrowTargetApp (x : (KernelPair.kernelPair.{u + 1, u, u + 1} (atlas G)).total) :
    (toFunctor (quotientKernelToArrow G ≫ toGroupoids.map G.t.left)).obj x ≅
      (toFunctor (KernelPair.pr0.{u + 1, u, u + 1} (atlas G))).obj x where
  hom := Quiver.Hom.op
    ⟨((sndBaseIso x ≪≫ (fstBaseIso x).symm).hom).op, sorry⟩
  inv := Quiver.Hom.op
    ⟨((sndBaseIso x ≪≫ (fstBaseIso x).symm).inv).op, sorry⟩
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The reverse comparison preserves the second projection as the actual source map. -/
def quotientKernelToArrow_sourceIso :
    quotientKernelToArrow G ≫ toGroupoids.map G.s.left ≅ KernelPair.pr1.{u + 1, u, u + 1} (atlas G) :=
  BasedFunctorIso.lift
    (ofComponents ((quotientKernelToArrowSourceApp G)) (fun {_ _} _ ↦ sorry) (fun _ ↦ sorry))

/-- The reverse comparison preserves the first projection as the actual target map. -/
def quotientKernelToArrow_targetIso :
    quotientKernelToArrow G ≫ toGroupoids.map G.t.left ≅ KernelPair.pr0.{u + 1, u, u + 1} (atlas G) :=
  BasedFunctorIso.lift
    (ofComponents ((quotientKernelToArrowTargetApp G)) (fun {_ _} _ ↦ sorry) (fun _ ↦ sorry))

end AlgebraicGeometry.GroupoidAlgebraicSpace.SmallQuotient
