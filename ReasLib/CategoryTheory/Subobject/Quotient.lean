/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Abelian.Exact
public import Mathlib.CategoryTheory.EffectiveEpi.Comp
public import Mathlib.CategoryTheory.ExtremalEpi
public import ReasLib.CategoryTheory.Subobject.Cardinal
public import ReasLib.CategoryTheory.Subobject.Kernel
public import ReasLib.CategoryTheory.Subobject.Quotient.Map
public import ReasLib.CategoryTheory.Subobject.Quotient.Intersection

@[expose] public section

/-!
# Subobject Quotients and Subquotients

Reusable infrastructure for quotient maps between subobjects and the subquotient construction.

Given subobjects `X ≤ Y` of an object `A`, we construct:
- `subobjectQuotientMap hXY : cokernel X.arrow ⟶ cokernel Y.arrow`, the canonical map `A/X → A/Y`
- `subobjectSubquotient hXY`, the object `Y/X` realized as the kernel of that map
- `IsSubquotient X Y`, the predicate asserting `X` is isomorphic to some `Y₂/Y₁` inside `Y`
- `subobjectSubquotient_isSubquotient_of_le_chain`, the main transitivity theorem
-/

open CategoryTheory.Limits

universe v u

noncomputable section

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

section QuotientMap

variable [HasZeroMorphisms C] [HasCokernels C]

/-- The inclusion `X ≤ Y` identifies `X.arrow` with `Subobject.ofLE X Y hXY ≫ Y.arrow`, so the
cokernel projection of `Y.arrow` annihilates `X.arrow`. -/
theorem subobjectQuotientMapCondition {A : C} {X Y : Subobject A} (hXY : X ≤ Y) :
    X.arrow ≫ cokernel.π Y.arrow = 0 := by
  rw [← Subobject.ofLE_arrow (X := X) (Y := Y) hXY, Category.assoc]
  simp

/-- The canonical morphism `A / X ⟶ A / Y` induced by an inclusion `X ≤ Y` of subobjects. -/
def subobjectQuotientMap {A : C} {X Y : Subobject A} (hXY : X ≤ Y) :
    cokernel X.arrow ⟶ cokernel Y.arrow :=
  cokernel.desc X.arrow (cokernel.π Y.arrow) (subobjectQuotientMapCondition hXY)

@[simp]
theorem subobjectQuotientMap_π {A : C} {X Y : Subobject A} (hXY : X ≤ Y) :
    cokernel.π X.arrow ≫ subobjectQuotientMap hXY = cokernel.π Y.arrow := by
  simp [subobjectQuotientMap]

/-- Quotient maps along a chain of subobjects compose to the direct quotient map. -/
theorem subobjectQuotientMap_comp {A : C} {W X Y : Subobject A}
    (hWX : W ≤ X) (hXY : X ≤ Y) :
    subobjectQuotientMap hWX ≫ subobjectQuotientMap hXY =
      subobjectQuotientMap (hWX.trans hXY) := by
  apply (cancel_epi (cokernel.π W.arrow)).1
  simp [subobjectQuotientMap]

end QuotientMap

section Subquotients

variable [HasZeroMorphisms C] [HasKernels C] [HasCokernels C]

/-- The subquotient `Y / X`, realized as the kernel subobject of the canonical map
`A / X ⟶ A / Y`. -/
def subobjectSubquotient {A : C} {X Y : Subobject A} (hXY : X ≤ Y) : C :=
  kernelSubobject (subobjectQuotientMap hXY)

/-- The canonical subobject of `A / X` whose underlying object is the subquotient
`subobjectSubquotient hXY = Y / X`. -/
abbrev subobjectSubquotientSubobject {A : C} {X Y : Subobject A} (hXY : X ≤ Y) :
    Subobject (cokernel X.arrow) :=
  kernelSubobject (subobjectQuotientMap hXY)

end Subquotients

section IsSubquotient

variable [Abelian C]

/-- An object `X` is a subquotient of `Y` if it is isomorphic to `Y₂ / Y₁` for some subobjects
`Y₁ ≤ Y₂ ≤ Y`. -/
def IsSubquotient (X Y : C) : Prop :=
  ∃ (Y₁ Y₂ : Subobject Y) (hY₁Y₂ : Y₁ ≤ Y₂), Nonempty (X ≅ subobjectSubquotient hY₁Y₂)

namespace IsSubquotient

/-- Transport `IsSubquotient` along an isomorphism on the left object. -/
theorem of_iso {X X' Y : C} (e : X ≅ X') :
    IsSubquotient X' Y → IsSubquotient X Y := by
  rintro ⟨Y₁, Y₂, hY₁Y₂, ⟨i⟩⟩
  exact ⟨Y₁, Y₂, hY₁Y₂, ⟨e ≪≫ i⟩⟩

/-- Transport `IsSubquotient` along an isomorphism of the ambient object. -/
@[stacks 012Q "subquotients under isomorphic ambient objects"]
theorem of_iso_right {X Y Y' : C} (e : Y ≅ Y') :
    IsSubquotient X Y → IsSubquotient X Y' := sorry

end IsSubquotient

/-- Every subobject arrow is the kernel of its quotient projection. -/
private theorem subobject_eq_kernel_cokernel {A : C} (X : Subobject A) :
    X = kernelSubobject (cokernel.π X.arrow) := by
  calc
    X = imageSubobject X.arrow := by
      symm
      simpa using (Limits.imageSubobject_mono X.arrow)
    _ = kernelSubobject (cokernel.π X.arrow) := by
      simpa using
        (ShortComplex.exact_iff_image_eq_kernel
          (ShortComplex.mk X.arrow (cokernel.π X.arrow) (cokernel.condition X.arrow))).1
          (ShortComplex.exact_cokernel X.arrow)

/-- Pushing a subobject forward along a morphism gives the image of the composite with the
ambient arrow. -/
private theorem exists_obj_eq_imageSubobject_comp {X Y : C} (f : X ⟶ Y) (S : Subobject X) :
    (Subobject.exists f).obj S = imageSubobject (S.arrow ≫ f) := by
  apply Subobject.eq_of_comm
    (Subobject.existsIsoImage f S ≪≫ (imageSubobjectIso _).symm)
  calc
    ((Subobject.existsIsoImage f S).hom ≫ (imageSubobjectIso (S.arrow ≫ f)).inv) ≫
        (imageSubobject (S.arrow ≫ f)).arrow
        = (Subobject.existsIsoImage f S).hom ≫ image.ι (S.arrow ≫ f) := by
            simp [Category.assoc]
    _ = ((Subobject.exists f).obj S).arrow := by
          have hw := Over.w ((Subobject.existsCompRepresentativeIso f).app S).hom.hom
          dsimp [Subobject.existsIsoImage] at hw ⊢
          exact hw

/-- Pulling the canonical subquotient `Y / X` back along the quotient map `A ⟶ A / X` recovers
the original subobject `Y ⊆ A`. -/
private theorem pullback_subobjectSubquotient_eq_subobject {A : C} {X Y : Subobject A}
    (hXY : X ≤ Y) :
    (Subobject.pullback (cokernel.π X.arrow)).obj (subobjectSubquotientSubobject hXY) = Y := by
  change (Subobject.pullback (cokernel.π X.arrow)).obj
      (kernelSubobject (subobjectQuotientMap hXY)) = Y
  calc
    (Subobject.pullback (cokernel.π X.arrow)).obj (kernelSubobject (subobjectQuotientMap hXY))
        = kernelSubobject (cokernel.π X.arrow ≫ subobjectQuotientMap hXY) := by
            symm
            exact
              kernelSubobject_comp_eq_pullback (cokernel.π X.arrow) (subobjectQuotientMap hXY)
    _ = kernelSubobject (cokernel.π Y.arrow) := by
          simp [subobjectQuotientMap]
    _ = Y := by
          rw [← subobject_eq_kernel_cokernel Y]

/-- The image of `Y ⟶ A / X` is exactly the canonical subobject representing `Y / X`. -/
private theorem imageSubobjectToQuotient_eq_subobjectSubquotient {A : C} {X Y : Subobject A}
    (hXY : X ≤ Y) :
    imageSubobject (Y.arrow ≫ cokernel.π X.arrow) = subobjectSubquotientSubobject hXY := by
  let π : A ⟶ cokernel X.arrow := cokernel.π X.arrow
  -- Local instance justification (defeq pin): the named quotient projection is used in the
  -- following calculation, while its epimorphism property should not be registered globally.
  letI : Epi π := by
    dsimp [π]
    infer_instance
  calc
    imageSubobject (Y.arrow ≫ π) = (Subobject.exists π).obj Y := by
      symm
      exact exists_obj_eq_imageSubobject_comp π Y
    _ = (Subobject.exists π).obj
          ((Subobject.pullback π).obj (subobjectSubquotientSubobject hXY)) := by
            rw [pullback_subobjectSubquotient_eq_subobject hXY]
    _ = subobjectSubquotientSubobject hXY := by
          exact Subobject.exists_obj_pullback_obj_eq_of_epi π (subobjectSubquotientSubobject hXY)

/-- Inside the ambient quotient `A / W`, the stage `X / W` lies below the stage `Y / W`. -/
private theorem subobjectSubquotientSubobject_le {A : C} {W X Y : Subobject A}
    (hWX : W ≤ X) (hXY : X ≤ Y) :
    subobjectSubquotientSubobject hWX ≤
      subobjectSubquotientSubobject (show W ≤ Y from hWX.trans hXY) := by
  refine le_kernelSubobject _ _ ?_
  rw [← subobjectQuotientMap_comp (hWX := hWX) (hXY := hXY)]
  have hzero := kernelSubobject_arrow_comp (subobjectQuotientMap hWX)
  rw [← Category.assoc, hzero]
  simp

/-- The canonical map `Y ⟶ Y / X`. -/
noncomputable abbrev subobjectToSubquotient {A : C} {X Y : Subobject A} (hXY : X ≤ Y) :
    (Y : C) ⟶ subobjectSubquotient (A := A) (X := X) (Y := Y) hXY :=
  factorThruKernelSubobject
    (subobjectQuotientMap hXY)
    (Y.arrow ≫ cokernel.π X.arrow)
    (by
      calc
        (Y.arrow ≫ cokernel.π X.arrow) ≫ subobjectQuotientMap hXY
            = Y.arrow ≫ (cokernel.π X.arrow ≫ subobjectQuotientMap hXY) := by
                simp [Category.assoc]
        _ = Y.arrow ≫ cokernel.π Y.arrow := by
              simp [subobjectQuotientMap]
        _ = 0 := cokernel.condition Y.arrow)

/-- The canonical map `Y ⟶ Y / X` followed by the subobject inclusion into `A / X` is the
usual quotient map out of `Y`. -/
theorem subobjectToSubquotient_comp_subobjectSubquotientInclusion {A : C}
    {X Y : Subobject A} (hXY : X ≤ Y) :
    subobjectToSubquotient hXY ≫ (subobjectSubquotientSubobject hXY).arrow =
      Y.arrow ≫ cokernel.π X.arrow := by
  change
    factorThruKernelSubobject
      (subobjectQuotientMap hXY)
      (Y.arrow ≫ cokernel.π X.arrow)
      (by
        calc
          (Y.arrow ≫ cokernel.π X.arrow) ≫ subobjectQuotientMap hXY
              = Y.arrow ≫ (cokernel.π X.arrow ≫ subobjectQuotientMap hXY) := by
                  simp [Category.assoc]
          _ = Y.arrow ≫ cokernel.π Y.arrow := by
                simp [subobjectQuotientMap]
          _ = 0 := cokernel.condition Y.arrow) ≫
        (subobjectSubquotientSubobject hXY).arrow =
      Y.arrow ≫ cokernel.π X.arrow
  rw [factorThruKernelSubobject_comp_arrow]

/-- The canonical inclusion of `Y / X` into `A / X` is a monomorphism. -/
instance subobjectSubquotientSubobject_arrow_mono {A : C} {X Y : Subobject A}
    (hXY : X ≤ Y) : Mono (subobjectSubquotientSubobject hXY).arrow := by
  change Mono (kernelSubobject (subobjectQuotientMap hXY)).arrow
  infer_instance

/-- Inside `Y`, the kernel of `Y ⟶ A / X` is exactly the subobject `X ⊆ Y`. -/
private theorem kernelSubobject_toQuotient_eq_subobjectOfLE {A : C} {X Y : Subobject A}
    (hXY : X ≤ Y) :
    kernelSubobject (Y.arrow ≫ cokernel.π X.arrow) = Subobject.mk (Subobject.ofLE X Y hXY) := by
  apply le_antisymm
  · rw [← Subobject.mk_arrow (kernelSubobject (Y.arrow ≫ cokernel.π X.arrow))]
    refine Subobject.mk_le_mk_of_comm
      (X.factorThru ((kernelSubobject (Y.arrow ≫ cokernel.π X.arrow)).arrow ≫ Y.arrow) ?_) ?_
    · have hFactorsKernel : (kernelSubobject (cokernel.π X.arrow)).Factors
          ((kernelSubobject (Y.arrow ≫ cokernel.π X.arrow)).arrow ≫ Y.arrow) := by
        rw [kernelSubobject_factors_iff]
        simpa [Category.assoc] using kernelSubobject_arrow_comp (Y.arrow ≫ cokernel.π X.arrow)
      have hXkernel : X = kernelSubobject (cokernel.π X.arrow) := by
        exact subobject_eq_kernel_cokernel X
      simpa [hXkernel] using hFactorsKernel
    · apply (cancel_mono Y.arrow).1
      simpa [Category.assoc, Subobject.ofLE_arrow] using
        (Subobject.factorThru_arrow X
          ((kernelSubobject (Y.arrow ≫ cokernel.π X.arrow)).arrow ≫ Y.arrow) _)
  · rw [← Subobject.mk_arrow (kernelSubobject (Y.arrow ≫ cokernel.π X.arrow))]
    refine Subobject.mk_le_mk_of_comm
      (factorThruKernelSubobject (Y.arrow ≫ cokernel.π X.arrow) (Subobject.ofLE X Y hXY) ?_) ?_
    · simpa [Category.assoc, Subobject.ofLE_arrow] using cokernel.condition X.arrow
    · rw [factorThruKernelSubobject_comp_arrow]

/-- The canonical map `Y ⟶ Y / X` kills the subobject `X ⊆ Y`. -/
theorem subobjectToSubquotient_comp_zero {A : C} {X Y : Subobject A} (hXY : X ≤ Y) :
    Subobject.ofLE X Y hXY ≫ subobjectToSubquotient hXY = 0 := by
  refine (cancel_mono (subobjectSubquotientSubobject hXY).arrow).1 ?_
  calc
    (Subobject.ofLE X Y hXY ≫ subobjectToSubquotient hXY) ≫
        (subobjectSubquotientSubobject hXY).arrow
        = Subobject.ofLE X Y hXY ≫ (Y.arrow ≫ cokernel.π X.arrow) := by
            rw [Category.assoc, subobjectToSubquotient_comp_subobjectSubquotientInclusion]
    _ = X.arrow ≫ cokernel.π X.arrow := by
          simp
    _ = 0 := cokernel.condition X.arrow
    _ = 0 ≫ (subobjectSubquotientSubobject hXY).arrow := by
          simp

/-- The canonical quotient map `Y ⟶ Y / X` is an epimorphism. -/
theorem subobjectToSubquotient_epi {A : C} {X Y : Subobject A} (hXY : X ≤ Y) :
    Epi (subobjectToSubquotient hXY) := by
  let e :
      (imageSubobject (Y.arrow ≫ cokernel.π X.arrow) : C) ≅ subobjectSubquotient hXY :=
    Subobject.isoOfEq _ _ (imageSubobjectToQuotient_eq_subobjectSubquotient hXY)
  have hComp :
      factorThruImageSubobject (Y.arrow ≫ cokernel.π X.arrow) ≫ e.hom =
        subobjectToSubquotient hXY := by
    have he_arrow :
        e.hom ≫ (subobjectSubquotientSubobject hXY).arrow =
          (imageSubobject (Y.arrow ≫ cokernel.π X.arrow)).arrow := by
      change
        Subobject.ofLE (imageSubobject (Y.arrow ≫ cokernel.π X.arrow))
            (subobjectSubquotientSubobject hXY)
            (imageSubobjectToQuotient_eq_subobjectSubquotient hXY).le ≫
          (subobjectSubquotientSubobject hXY).arrow =
        (imageSubobject (Y.arrow ≫ cokernel.π X.arrow)).arrow
      exact
        Subobject.ofLE_arrow
          (h := (imageSubobjectToQuotient_eq_subobjectSubquotient hXY).le)
    refine (cancel_mono (subobjectSubquotientSubobject hXY).arrow).1 ?_
    calc
      (factorThruImageSubobject (Y.arrow ≫ cokernel.π X.arrow) ≫ e.hom) ≫
          (subobjectSubquotientSubobject hXY).arrow
          = factorThruImageSubobject (Y.arrow ≫ cokernel.π X.arrow) ≫
              (imageSubobject (Y.arrow ≫ cokernel.π X.arrow)).arrow := by
                rw [Category.assoc, he_arrow]
      _ = Y.arrow ≫ cokernel.π X.arrow := by
            rw [imageSubobject_arrow_comp]
      _ = subobjectToSubquotient hXY ≫ (subobjectSubquotientSubobject hXY).arrow := by
            symm
            exact subobjectToSubquotient_comp_subobjectSubquotientInclusion hXY
  -- Local instance justification (proof-local temporary data): these epimorphism facts only
  -- support the final cancellation step and do not define canonical ambient instances.
  letI : Epi (factorThruImageSubobject (Y.arrow ≫ cokernel.π X.arrow)) := inferInstance
  letI : Epi e.hom := inferInstance
  haveI : Epi (factorThruImageSubobject (Y.arrow ≫ cokernel.π X.arrow) ≫ e.hom) := inferInstance
  simpa [hComp]

/-- The canonical quotient map `Y ⟶ Y / X` is available to typeclass search. -/
instance instEpiSubobjectToSubquotient {A : C} {X Y : Subobject A} (hXY : X ≤ Y) :
    Epi (subobjectToSubquotient hXY) :=
  subobjectToSubquotient_epi hXY

/-- The canonical sequence `0 ⟶ X ⟶ Y ⟶ Y / X ⟶ 0` is short exact. -/
theorem subobjectToSubquotient_shortExact {A : C} {X Y : Subobject A} (hXY : X ≤ Y) :
    (ShortComplex.mk (Subobject.ofLE X Y hXY) (subobjectToSubquotient hXY)
      (subobjectToSubquotient_comp_zero hXY)).ShortExact := by
  refine ShortComplex.ShortExact.mk' ?_ inferInstance inferInstance
  rw [ShortComplex.exact_iff_image_eq_kernel]
  have hKernel :
      kernelSubobject (subobjectToSubquotient hXY) = Subobject.mk (Subobject.ofLE X Y hXY) := by
    calc
      kernelSubobject (subobjectToSubquotient hXY)
          = kernelSubobject
              (subobjectToSubquotient hXY ≫ (subobjectSubquotientSubobject hXY).arrow) := by
                have hMono : Mono (subobjectSubquotientSubobject hXY).arrow :=
                  subobjectSubquotientSubobject_arrow_mono hXY
                symm
                exact
                  @Limits.kernelSubobject_comp_mono _ _ _ _ _ (subobjectToSubquotient hXY)
                    inferInstance _ (subobjectSubquotientSubobject hXY).arrow hMono
      _ = kernelSubobject (Y.arrow ≫ cokernel.π X.arrow) := by
            rw [subobjectToSubquotient_comp_subobjectSubquotientInclusion]
      _ = Subobject.mk (Subobject.ofLE X Y hXY) := by
            exact kernelSubobject_toQuotient_eq_subobjectOfLE hXY
  calc
    imageSubobject (Subobject.ofLE X Y hXY) = Subobject.mk (Subobject.ofLE X Y hXY) := by
      simpa using (Limits.imageSubobject_mono (Subobject.ofLE X Y hXY))
    _ = kernelSubobject (subobjectToSubquotient hXY) := by
      symm
      exact hKernel

/-- The canonical map `Y ⟶ Y / X` is a cokernel of the inclusion `X ⟶ Y`. -/
noncomputable def subobjectToSubquotient_isCokernel {A : C} {X Y : Subobject A}
    (hXY : X ≤ Y) :
    IsColimit (CokernelCofork.ofπ (subobjectToSubquotient hXY)
      (subobjectToSubquotient_comp_zero hXY)) := by
  exact (subobjectToSubquotient_shortExact hXY).gIsCokernel

namespace Subobject.Subquotient

/-- The kernel-subobject representative of `Y / X` is isomorphic to the direct cokernel of the
inclusion `X ⟶ Y`. -/
@[stacks 012M "subquotient direct-cokernel comparison"]
theorem isIsomorphicCokernel {A : C} {X Y : Subobject A} (hXY : X ≤ Y) :
    IsIsomorphic (subobjectSubquotient hXY) (cokernel (Subobject.ofLE X Y hXY)) := sorry

/-- There is a comparison isomorphism from the kernel-subobject representative of `Y / X` to
the direct cokernel which carries the canonical quotient map to the cokernel projection. -/
@[stacks 012M "subquotient comparison projection"]
theorem exists_isoCokernel {A : C} {X Y : Subobject A} (hXY : X ≤ Y) :
    ∃ e : subobjectSubquotient hXY ≅ cokernel (Subobject.ofLE X Y hXY),
      subobjectToSubquotient hXY ≫ e.hom = cokernel.π (Subobject.ofLE X Y hXY) := sorry

end Subobject.Subquotient

/-- Any epi `Y ⟶ T` with kernel `X ⊆ Y` identifies `T` with the canonical subquotient
`Y / X`. -/
private theorem subobjectSubquotientIsoOfEpi {A : C} {X Y : Subobject A} (hXY : X ≤ Y)
    {T : C} (f : (Y : C) ⟶ T) [Epi f]
    (hKernel : kernelSubobject f = Subobject.mk (Subobject.ofLE X Y hXY)) :
    Nonempty (subobjectSubquotient hXY ≅ T) := by
  have hFactors : (kernelSubobject f).Factors (Subobject.ofLE X Y hXY) := by
    simpa [hKernel] using
      (Subobject.mk_factors_self (Subobject.ofLE X Y hXY) :
        (Subobject.mk (Subobject.ofLE X Y hXY)).Factors (Subobject.ofLE X Y hXY))
  have hzero : Subobject.ofLE X Y hXY ≫ f = 0 := by
    exact (kernelSubobject_factors_iff f (Subobject.ofLE X Y hXY)).1 hFactors
  have hExact :
      (ShortComplex.mk (Subobject.ofLE X Y hXY) f hzero).Exact := by
    rw [ShortComplex.exact_iff_image_eq_kernel]
    calc
      imageSubobject (Subobject.ofLE X Y hXY) = Subobject.mk (Subobject.ofLE X Y hXY) := by
        simpa using (Limits.imageSubobject_mono (Subobject.ofLE X Y hXY))
      _ = kernelSubobject f := by
        simpa using hKernel.symm
  have hShort :
      (ShortComplex.mk (Subobject.ofLE X Y hXY) f hzero).ShortExact := by
    exact ShortComplex.ShortExact.mk' hExact inferInstance inferInstance
  exact ⟨IsColimit.coconePointUniqueUpToIso (subobjectToSubquotient_isCokernel hXY)
    (ShortComplex.ShortExact.gIsCokernel hShort)⟩

/-- An epi from a subobject `Q ≤ S` presents its codomain as a subquotient of `S`. -/
private theorem isSubquotient_of_epi_of_le {B T : C} {Q S : Subobject B}
    (hQS : Q ≤ S) (f : (Q : C) ⟶ T) [Epi f] :
    IsSubquotient T (S : C) := by
  let QS : Subobject (S : C) := Subobject.mk (Subobject.ofLE Q S hQS)
  let KS : Subobject (S : C) := Subobject.mk ((kernelSubobject f).arrow ≫ Subobject.ofLE Q S hQS)
  have hKSQS : KS ≤ QS := by
    change Subobject.mk ((kernelSubobject f).arrow ≫ Subobject.ofLE Q S hQS) ≤
        Subobject.mk (Subobject.ofLE Q S hQS)
    exact Subobject.mk_le_mk_of_comm (kernelSubobject f).arrow (by simp)
  let eQ : (QS : C) ≅ (Q : C) := Subobject.underlyingIso (Subobject.ofLE Q S hQS)
  let g : (QS : C) ⟶ T := eQ.hom ≫ f
  -- Local instance justification (defeq pin): this transported epimorphism is needed only for
  -- the kernel comparison below and is not a canonical instance on arbitrary maps.
  letI : Epi g := by
    dsimp [g]
    infer_instance

  let eK : (KS : C) ≅ (kernelSubobject f : C) :=
    Subobject.underlyingIso ((kernelSubobject f).arrow ≫ Subobject.ofLE Q S hQS)
  have hKernel' : Subobject.mk (Subobject.ofLE KS QS hKSQS) = kernelSubobject g := by
    refine Subobject.mk_eq_of_comm (Subobject.ofLE KS QS hKSQS)
      (eK ≪≫ (kernelSubobjectIsoComp eQ.hom f).symm) ?_
    apply (cancel_mono QS.arrow).1
    calc
      ((eK ≪≫ (kernelSubobjectIsoComp eQ.hom f).symm).hom ≫
          (kernelSubobject g).arrow) ≫
          QS.arrow
          = eK.hom ≫ (((kernelSubobjectIsoComp eQ.hom f).symm).hom ≫
              (kernelSubobject g).arrow) ≫
              QS.arrow := by
                simp [Category.assoc]
      _ = eK.hom ≫ ((kernelSubobject f).arrow ≫ eQ.inv) ≫ QS.arrow := by
            simpa [g, Category.assoc] using
              congrArg (fun k => eK.hom ≫ k ≫ QS.arrow)
                (kernelSubobjectIsoComp_inv_arrow (f := eQ.hom) (g := f))
      _ = eK.hom ≫ (kernelSubobject f).arrow ≫ (eQ.inv ≫ QS.arrow) := by
            simp [Category.assoc]
      _ = eK.hom ≫ (kernelSubobject f).arrow ≫ Subobject.ofLE Q S hQS := by
            rw [Subobject.underlyingIso_arrow]
      _ = KS.arrow := by
            simpa [eK, KS] using
              (Subobject.underlyingIso_hom_comp_eq_mk
                ((kernelSubobject f).arrow ≫ Subobject.ofLE Q S hQS))
      _ = Subobject.ofLE KS QS hKSQS ≫ QS.arrow := by
            rw [Subobject.ofLE_arrow]
  have hKernel : kernelSubobject g = Subobject.mk (Subobject.ofLE KS QS hKSQS) := hKernel'.symm
  obtain ⟨e⟩ := subobjectSubquotientIsoOfEpi hKSQS g hKernel
  have hBase : IsSubquotient (subobjectSubquotient hKSQS) (S : C) := by
    exact ⟨KS, QS, hKSQS, ⟨Iso.refl _⟩⟩
  exact IsSubquotient.of_iso e.symm hBase

/-- The quotient map `Y ⟶ Y / X` already kills the smaller subobject `W ⊆ Y` whenever
`W ≤ X ≤ Y`. -/
private theorem subobjectToSubquotient_comp_zero_of_le_chain {A : C} {W X Y : Subobject A}
    (hWX : W ≤ X) (hXY : X ≤ Y) :
    Subobject.ofLE W Y (show W ≤ Y from hWX.trans hXY) ≫ subobjectToSubquotient hXY = 0 := by
  calc
    Subobject.ofLE W Y (show W ≤ Y from hWX.trans hXY) ≫ subobjectToSubquotient hXY
        = (Subobject.ofLE W X hWX ≫ Subobject.ofLE X Y hXY) ≫ subobjectToSubquotient hXY := by
              rw [Subobject.ofLE_comp_ofLE W X Y hWX hXY]
    _ = Subobject.ofLE W X hWX ≫
            (Subobject.ofLE X Y hXY ≫ subobjectToSubquotient hXY) := by
          rw [Category.assoc]
    _ = Subobject.ofLE W X hWX ≫ 0 := by
          rw [subobjectToSubquotient_comp_zero hXY]
    _ = 0 := by
          simp

/-- The quotient map `Y ⟶ Y / X` descends along the quotient `Y ⟶ Y / W` when
`W ≤ X ≤ Y`. -/
private noncomputable def stageToSubobjectSubquotient {A : C} {W X Y : Subobject A}
    (hWX : W ≤ X) (hXY : X ≤ Y) :
    subobjectSubquotient (show W ≤ Y from hWX.trans hXY) ⟶ subobjectSubquotient hXY :=
  (subobjectToSubquotient_isCokernel (show W ≤ Y from hWX.trans hXY)).desc <|
    CokernelCofork.ofπ (subobjectToSubquotient hXY)
      (subobjectToSubquotient_comp_zero_of_le_chain hWX hXY)

/-- The descended map from `Y / W` to `Y / X` composes with the canonical quotient `Y ⟶ Y / W`
to recover the map `Y ⟶ Y / X`. -/
private theorem subobjectToSubquotient_comp_stageToSubobjectSubquotient {A : C}
    {W X Y : Subobject A} (hWX : W ≤ X) (hXY : X ≤ Y) :
    subobjectToSubquotient (show W ≤ Y from hWX.trans hXY) ≫
        stageToSubobjectSubquotient hWX hXY =
      subobjectToSubquotient hXY := by
  have h := (subobjectToSubquotient_isCokernel (show W ≤ Y from hWX.trans hXY)).fac
      (CokernelCofork.ofπ (subobjectToSubquotient hXY)
        (subobjectToSubquotient_comp_zero_of_le_chain hWX hXY))
      WalkingParallelPair.one
  dsimp at h
  exact h

/-- The descended map `Y / W ⟶ Y / X` is an epimorphism. -/
private theorem stageToSubobjectSubquotient_epi {A : C} {W X Y : Subobject A}
    (hWX : W ≤ X) (hXY : X ≤ Y) :
    Epi (stageToSubobjectSubquotient hWX hXY) := by
  exact epi_of_epi_fac (subobjectToSubquotient_comp_stageToSubobjectSubquotient hWX hXY)

/-- If `W ≤ X ≤ Y ≤ Z` are subobjects of `A`, then the intermediate quotient `Y / X` is a
subquotient of the larger quotient `Z / W`. -/
theorem subobjectSubquotient_isSubquotient_of_le_chain {A : C} {W X Y Z : Subobject A}
    (hWX : W ≤ X) (hXY : X ≤ Y) (hYZ : Y ≤ Z) :
    IsSubquotient (subobjectSubquotient hXY)
      (subobjectSubquotient (hWX.trans <| hXY.trans hYZ)) := by
  let hWY : W ≤ Y := show W ≤ Y from hWX.trans hXY
  let hWZ : W ≤ Z := show W ≤ Z from hWX.trans (hXY.trans hYZ)
  have hEpi : Epi (stageToSubobjectSubquotient hWX hXY) := stageToSubobjectSubquotient_epi hWX hXY
  exact
    @isSubquotient_of_epi_of_le C _ _ (cokernel W.arrow) (subobjectSubquotient hXY)
      (subobjectSubquotientSubobject hWY) (subobjectSubquotientSubobject hWZ)
      (subobjectSubquotientSubobject_le hWY hYZ)
      (stageToSubobjectSubquotient hWX hXY) hEpi

end IsSubquotient

end CategoryTheory
