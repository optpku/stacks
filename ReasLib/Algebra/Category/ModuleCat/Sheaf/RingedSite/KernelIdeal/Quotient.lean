/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Ideal.Quotient
public import ReasLib.CategoryTheory.Sites.LocalIsoDescent
import Mathlib.Tactic.CrossRefAttribute

/-!
@stack 0B8S

# The quotient by the kernel of a locally surjective ring-sheaf morphism

A morphism of sheaves of commutative rings induces a canonical map from the quotient by its
kernel.  This map is an isomorphism when the original morphism is locally surjective.  Local
surjectivity is essential here: a categorical epimorphism of commutative rings need not be a
surjective ring homomorphism.
-/

@[expose] public section

open CategoryTheory Opposite

noncomputable section

universe u v w

namespace SheafOfModules.RingedSite.KernelIdeal

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable {A Q : Sheaf J CommRingCat.{w}}
variable [HasWeakSheafify J CommRingCat.{w}]

/-- The canonical map `A / ker π ⟶ Q` induced by a morphism of ring sheaves `π : A ⟶ Q`. -/
@[stacks 0B8S "quotient comparison for a square-zero extension"]
noncomputable abbrev quotientComparison (π : A ⟶ Q) :
    IdealSheaf.Quotient.sheaf (subobject π) ⟶ Q :=
  IdealSheaf.Quotient.lift (subobject π) π le_rfl

/-- The quotient projection followed by `quotientComparison π` is `π`. -/
@[reassoc, simp, stacks 0B8S "quotient comparison factorization"]
theorem projection_comp_quotientComparison (π : A ⟶ Q) :
    IdealSheaf.Quotient.projection (subobject π) ≫ quotientComparison π = π := sorry

/-- `quotientComparison π` is the unique map from `A / ker π` whose composite with the
quotient projection is `π`. -/
@[stacks 0B8S "uniqueness of the quotient comparison"]
theorem quotientComparison_unique (π : A ⟶ Q)
    (f : IdealSheaf.Quotient.sheaf (subobject π) ⟶ Q)
    (hf : IdealSheaf.Quotient.projection (subobject π) ≫ f = π) :
    f = quotientComparison π := sorry

section LocalComparison

/-- Quotienting by the kernel makes the induced comparison locally injective. -/
@[stacks 0B8S "local injectivity of the quotient comparison"]
instance quotientComparison_isLocallyInjective (π : A ⟶ Q)
    [hW : J.WEqualsLocallyBijective CommRingCat.{w}] :
    Sheaf.IsLocallyInjective (quotientComparison π) := sorry

/-- A locally surjective morphism induces a locally surjective quotient comparison. -/
@[stacks 0B8S "local surjectivity of the quotient comparison"]
instance quotientComparison_isLocallySurjective (π : A ⟶ Q)
    [Sheaf.IsLocallySurjective π] :
    Sheaf.IsLocallySurjective (quotientComparison π) := sorry

/-- The underlying type-valued quotient comparison, retaining the original map on sections. -/
abbrev quotientComparisonTypes (π : A ⟶ Q) :=
  ((sheafCompose J (CategoryTheory.forget CommRingCat.{w})).map (quotientComparison π)).hom

/-- The actual quotient sheaf, with its ring structure forgotten to a type sheaf. -/
abbrev quotientTypeSheaf (π : A ⟶ Q) :=
  (sheafCompose J (CategoryTheory.forget CommRingCat.{w})).obj
    (IdealSheaf.Quotient.sheaf (subobject π))

/-- Local injectivity remains true after forgetting the quotient comparison's ring structure. -/
instance quotientComparisonTypes_isLocallyInjective (π : A ⟶ Q)
    [J.WEqualsLocallyBijective CommRingCat.{w}] :
    Presheaf.IsLocallyInjective J (quotientComparisonTypes π) := by
  letI := quotientComparison_isLocallyInjective π
  infer_instance

/-- Local lifts to the quotient remain available after forgetting ring structure. -/
instance quotientComparisonTypes_isLocallySurjective (π : A ⟶ Q)
    [Sheaf.IsLocallySurjective π] :
    Presheaf.IsLocallySurjective J (quotientComparisonTypes π) := by
  letI := quotientComparison_isLocallySurjective π
  infer_instance

/-- A target section is lifted locally to actual quotient sections and those sections are
amalgamated using the quotient sheaf condition. The function is independent of inverse laws. -/
def quotientInverseSection (π : A ⟶ Q)
    [J.WEqualsLocallyBijective CommRingCat.{w}] [Sheaf.IsLocallySurjective π]
    (U : Cᵒᵖ) (q : Q.obj.obj U) : (IdealSheaf.Quotient.sheaf (subobject π)).obj.obj U :=
  Presheaf.LocalIsoDescent.app J (quotientComparisonTypes π) (𝟙 (quotientTypeSheaf π).obj)
    (quotientTypeSheaf π).property q

/-- The local quotient lifts form the specified ring map on each section object. -/
def quotientInverseApp (π : A ⟶ Q)
    [J.WEqualsLocallyBijective CommRingCat.{w}] [Sheaf.IsLocallySurjective π]
    (U : Cᵒᵖ) : Q.obj.obj U ⟶ (IdealSheaf.Quotient.sheaf (subobject π)).obj.obj U :=
  CommRingCat.ofHom
    { toFun := quotientInverseSection π U
      map_zero' := sorry
      map_one' := sorry
      map_add' := sorry
      map_mul' := sorry }

/-- The concrete inverse comparison obtained by sheaf amalgamation of quotient sections. -/
def quotientComparisonInv (π : A ⟶ Q)
    [J.WEqualsLocallyBijective CommRingCat.{w}] [Sheaf.IsLocallySurjective π] :
    Q ⟶ IdealSheaf.Quotient.sheaf (subobject π) :=
  ⟨{ app := quotientInverseApp π, naturality := sorry }⟩

/-- The first-isomorphism comparison has explicit section functions in both directions. -/
@[stacks 0B8S "actual quotient comparison isomorphism"]
def quotientComparisonIso (π : A ⟶ Q)
    [J.WEqualsLocallyBijective CommRingCat.{w}] [Sheaf.IsLocallySurjective π] :
    IdealSheaf.Quotient.sheaf (subobject π) ≅ Q where
  hom := quotientComparison π
  inv := quotientComparisonInv π
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The first isomorphism theorem uses the specified local-lift inverse. -/
@[stacks 0B8S "first isomorphism theorem for a locally surjective ring-sheaf morphism"]
instance quotientComparison_isIso (π : A ⟶ Q)
    [hW : J.WEqualsLocallyBijective CommRingCat.{w}]
    [Sheaf.IsLocallySurjective π] : IsIso (quotientComparison π) :=
  (quotientComparisonIso π).isIso_hom

/-- The quotient comparison upgraded to an isomorphism using a caller-supplied invertibility
certificate. For the locally surjective instance, that certificate stores the local-lift inverse
of `quotientComparisonIso`. -/
@[stacks 0B8S "quotient comparison isomorphism"]
noncomputable def quotientIso (π : A ⟶ Q)
    (h : IsIso (quotientComparison π)) :
    IdealSheaf.Quotient.sheaf (subobject π) ≅ Q :=
  @asIso _ _ _ _ (quotientComparison π) h

/-- The forward map of `quotientIso π h` is the canonical quotient comparison. -/
@[simp, stacks 0B8S "quotient comparison isomorphism forward map"]
theorem quotientIso_hom (π : A ⟶ Q) (h : IsIso (quotientComparison π)) :
    (quotientIso π h).hom = quotientComparison π := sorry

/-- Under local surjectivity, every invertibility certificate has the specified local-lift
inverse. This also specifies the value selected by the generic certificate interface. -/
@[simp]
theorem quotientIso_inv (π : A ⟶ Q)
    [J.WEqualsLocallyBijective CommRingCat.{w}] [Sheaf.IsLocallySurjective π]
    (h : IsIso (quotientComparison π)) :
    (quotientIso π h).inv = quotientComparisonInv π := sorry

/-- The quotient comparison isomorphism is independent of the chosen invertibility certificate. -/
@[stacks 0B8S "quotient comparison isomorphism proof independence"]
theorem quotientIso_eq (π : A ⟶ Q) (h₁ h₂ : IsIso (quotientComparison π)) :
    quotientIso π h₁ = quotientIso π h₂ := sorry

/-- The quotient comparison viewed as an isomorphism of the underlying `RingCat`-valued sheaves. -/
@[stacks 0B8S "underlying ring-sheaf quotient comparison isomorphism"]
noncomputable abbrev quotientRingIso (π : A ⟶ Q)
    (h : IsIso (quotientComparison π)) :
    ringSheaf J (IdealSheaf.Quotient.sheaf (subobject π)) ≅ ringSheaf J Q :=
  (sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).mapIso (quotientIso π h)

/-- The scalar-transport inverse acts on sections by the actual local quotient amalgamation. -/
@[simp]
theorem quotientRingIso_inv_app (π : A ⟶ Q)
    [J.WEqualsLocallyBijective CommRingCat.{w}] [Sheaf.IsLocallySurjective π]
    (h : IsIso (quotientComparison π)) (U : Cᵒᵖ) (q : Q.obj.obj U) :
    (quotientRingIso π h).inv.hom.app U q = quotientInverseSection π U q := sorry

end LocalComparison

end SheafOfModules.RingedSite.KernelIdeal
