module

public import ReasLib.Algebra.Homology.DerivedCategory.InternalHom.Model.RHom.Unit
public import ReasLib.CategoryTheory.DerivedCategory.Monoidal.Tensor.Bifunctor.Unit
import Mathlib.Tactic.CrossRefAttribute

/-!
# Tensor-unit comparisons for the regular derived module

@stack 0E1U

This is the standard-universe ModuleCat specialization of the generic fixed-left derived tensor
unit comparison.  It keeps the ambient tensor model and the identification `A[0] ≅ 𝟙_`
explicit.  The existing `single0DerivedTensorIso` fixes `A[0]` on the right; declarations in this
file fix it on the left.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory CategoryTheory.MonoidalCategory

namespace CategoryTheory.DerivedCategory.InternalHom.RHom.Unit

variable {A : Type u} [CommRing A]

/-- `0E1U:` Pair the regular degree-zero object with a varying second tensor factor. -/
@[stacks 0E1U "regular degree-zero fixed-left pair functor"]
noncomputable abbrev singlePair :
    DerivedCategory (ModuleCat.{u} A) ⥤
      DerivedCategory (ModuleCat.{u} A) × DerivedCategory (ModuleCat.{u} A) :=
  DerivedTensor.Bifunctor.Monoidal.Unit.pair (single (A := A))

section Tensor

variable [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))]

/-- `0E1U:` Compare `A[0] ⊗ᴸ K` with `K` from an explicit ambient tensor model and unit
identification.  This is the fixed-left companion of `single0DerivedTensorIso`. -/
@[stacks 0E1U "regular degree-zero fixed-left derived tensor comparison"]
noncomputable abbrev single0LeftDerivedTensorIso
    (T : DerivedTensor.Right.Monoidal.Model (C := ModuleCat.{u} A))
    (s : single (A := A) ≅ 𝟙_ (DerivedCategory (ModuleCat.{u} A)))
    (K : DerivedCategory (ModuleCat.{u} A))
    [DerivedTensor.Right.Has (C := ModuleCat.{u} A)] :
    DerivedTensor.Right.obj (single (A := A)) K ≅ K :=
  DerivedTensor.Bifunctor.Monoidal.Unit.leftUnitObjIso
    T (single (A := A)) s K

section Bifunctor

variable [∀ G₁ G₂ : GradedObject ℤ (ModuleCat.{u} A), GradedObject.HasTensor G₁ G₂]
variable [∀ G₁ G₂ G₃ : GradedObject ℤ (ModuleCat.{u} A),
  GradedObject.HasGoodTensor₁₂Tensor G₁ G₂ G₃]
variable [∀ G₁ G₂ G₃ : GradedObject ℤ (ModuleCat.{u} A),
  GradedObject.HasGoodTensorTensor₂₃ G₁ G₂ G₃]
variable [∀ G₁ G₂ G₃ G₄ : GradedObject ℤ (ModuleCat.{u} A),
  GradedObject.HasTensor₄ObjExt G₁ G₂ G₃ G₄]
variable [HomotopyCategory.Koszul.TensorDescends (C := ModuleCat.{u} A)]
variable [DerivedTensor.Right.Has (C := ModuleCat.{u} A)]
variable [DerivedTensor.Bifunctor.Has (C := ModuleCat.{u} A)]

/-- `0E1U:` The explicit two-variable naturality gate for the regular-module tensor comparison.
Pointwise fixed-right compatibility alone does not imply this proposition. -/
@[stacks 0E1U "regular-module bifunctor tensor comparison naturality"]
abbrev BifunctorComparisonIsNatural
    (T : DerivedTensor.Right.Monoidal.Model (C := ModuleCat.{u} A)) : Prop :=
  DerivedTensor.Bifunctor.Monoidal.IsNaturalOf T
    (fun E => ModuleCat.derivedTensorBifunctorRightCompatible A E)

/-- `0E1U:` The canonical two-variable derived tensor comparison after fixing its first variable
at the regular degree-zero object. -/
@[stacks 0E1U "regular degree-zero derived bifunctor unit comparison"]
noncomputable abbrev bifunctorLeftUnitIso
    (T : DerivedTensor.Right.Monoidal.Model (C := ModuleCat.{u} A))
    (hn : BifunctorComparisonIsNatural (A := A) T)
    (s : single (A := A) ≅ 𝟙_ (DerivedCategory (ModuleCat.{u} A))) :
    singlePair (A := A) ⋙ DerivedTensor.Bifunctor.functor (C := ModuleCat.{u} A) ≅
      𝟭 (DerivedCategory (ModuleCat.{u} A)) :=
  DerivedTensor.Bifunctor.Monoidal.Unit.functorIso T
    (fun E => ModuleCat.derivedTensorBifunctorRightCompatible A E)
    hn (single (A := A)) s

/-- The objectwise canonical two-variable regular-unit comparison. -/
@[stacks 0E1U "regular degree-zero derived bifunctor unit object comparison"]
noncomputable abbrev bifunctorLeftUnitObjIso
    (T : DerivedTensor.Right.Monoidal.Model (C := ModuleCat.{u} A))
    (hn : BifunctorComparisonIsNatural (A := A) T)
    (s : single (A := A) ≅ 𝟙_ (DerivedCategory (ModuleCat.{u} A)))
    (K : DerivedCategory (ModuleCat.{u} A)) :
    (singlePair (A := A) ⋙
      DerivedTensor.Bifunctor.functor (C := ModuleCat.{u} A)).obj K ≅ K :=
  (bifunctorLeftUnitIso (A := A) T hn s).app K

/-- Naturality of the canonical regular-unit bifunctor comparison. -/
@[reassoc, stacks 0E1U "regular degree-zero derived bifunctor unit naturality"]
theorem bifunctorLeftUnitIso_naturality
    (T : DerivedTensor.Right.Monoidal.Model (C := ModuleCat.{u} A))
    (hn : BifunctorComparisonIsNatural (A := A) T)
    (s : single (A := A) ≅ 𝟙_ (DerivedCategory (ModuleCat.{u} A)))
    {K L : DerivedCategory (ModuleCat.{u} A)} (f : K ⟶ L) :
    (singlePair (A := A) ⋙
        DerivedTensor.Bifunctor.functor (C := ModuleCat.{u} A)).map f ≫
        (bifunctorLeftUnitIso (A := A) T hn s).hom.app L =
      (bifunctorLeftUnitIso (A := A) T hn s).hom.app K ≫ f :=
  DerivedTensor.Bifunctor.Monoidal.Unit.functorIso_naturality T
    (fun E ↦ ModuleCat.derivedTensorBifunctorRightCompatible A E)
    hn (single (A := A)) s f

/-- Inverse naturality of the canonical regular-unit bifunctor comparison. -/
@[reassoc, stacks 0E1U "inverse regular degree-zero derived bifunctor unit naturality"]
theorem bifunctorLeftUnitIso_inv_naturality
    (T : DerivedTensor.Right.Monoidal.Model (C := ModuleCat.{u} A))
    (hn : BifunctorComparisonIsNatural (A := A) T)
    (s : single (A := A) ≅ 𝟙_ (DerivedCategory (ModuleCat.{u} A)))
    {K L : DerivedCategory (ModuleCat.{u} A)} (f : K ⟶ L) :
    f ≫ (bifunctorLeftUnitIso (A := A) T hn s).inv.app L =
      (bifunctorLeftUnitIso (A := A) T hn s).inv.app K ≫
        (singlePair (A := A) ⋙
          DerivedTensor.Bifunctor.functor (C := ModuleCat.{u} A)).map f :=
  DerivedTensor.Bifunctor.Monoidal.Unit.functorIso_inv_naturality T
    (fun E ↦ ModuleCat.derivedTensorBifunctorRightCompatible A E)
    hn (single (A := A)) s f

/-- The canonical bifunctor comparison agrees with the fixed-left object comparison. -/
@[simp, stacks 0E1U "regular derived bifunctor and fixed-left agreement"]
theorem bifunctorLeftUnitIso_agrees_hom
    (T : DerivedTensor.Right.Monoidal.Model (C := ModuleCat.{u} A))
    (hn : BifunctorComparisonIsNatural (A := A) T)
    (s : single (A := A) ≅ 𝟙_ (DerivedCategory (ModuleCat.{u} A)))
    (K : DerivedCategory (ModuleCat.{u} A)) :
    (DerivedTensor.Bifunctor.Right.isoAppOf K
          (ModuleCat.derivedTensorBifunctorRightCompatible A K)
          (single (A := A))).hom ≫
        (bifunctorLeftUnitIso (A := A) T hn s).hom.app K =
      (single0LeftDerivedTensorIso (A := A) T s K).hom :=
  DerivedTensor.Bifunctor.Monoidal.Unit.functorIso_agrees_hom T
    (fun E ↦ ModuleCat.derivedTensorBifunctorRightCompatible A E)
    hn (single (A := A)) s K

/-- The inverse canonical bifunctor comparison agrees with the fixed-left object comparison. -/
@[simp, stacks 0E1U "inverse regular derived bifunctor and fixed-left agreement"]
theorem bifunctorLeftUnitIso_agrees_inv
    (T : DerivedTensor.Right.Monoidal.Model (C := ModuleCat.{u} A))
    (hn : BifunctorComparisonIsNatural (A := A) T)
    (s : single (A := A) ≅ 𝟙_ (DerivedCategory (ModuleCat.{u} A)))
    (K : DerivedCategory (ModuleCat.{u} A)) :
    (bifunctorLeftUnitIso (A := A) T hn s).inv.app K ≫
        (DerivedTensor.Bifunctor.Right.isoAppOf K
          (ModuleCat.derivedTensorBifunctorRightCompatible A K)
          (single (A := A))).inv =
      (single0LeftDerivedTensorIso (A := A) T s K).inv :=
  DerivedTensor.Bifunctor.Monoidal.Unit.functorIso_agrees_inv T
    (fun E ↦ ModuleCat.derivedTensorBifunctorRightCompatible A E)
    hn (single (A := A)) s K

end Bifunctor

end Tensor

end CategoryTheory.DerivedCategory.InternalHom.RHom.Unit
