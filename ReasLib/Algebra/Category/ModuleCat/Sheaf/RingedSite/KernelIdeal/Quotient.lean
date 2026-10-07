module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Ideal.Quotient
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

/-- The first isomorphism theorem for a locally surjective morphism of sheaves of commutative
rings: the canonical map `A / ker π ⟶ Q` is an isomorphism. -/
@[stacks 0B8S "first isomorphism theorem for a locally surjective ring-sheaf morphism"]
instance quotientComparison_isIso (π : A ⟶ Q)
    [hW : J.WEqualsLocallyBijective CommRingCat.{w}]
    [Sheaf.IsLocallySurjective π] :
    IsIso (quotientComparison π) := sorry

/-- The quotient comparison upgraded to an isomorphism after an explicit invertibility
certificate.  Keeping the certificate explicit prevents hidden choice of inverse data. -/
@[stacks 0B8S "quotient comparison isomorphism"]
noncomputable def quotientIso (π : A ⟶ Q)
    (h : IsIso (quotientComparison π)) :
    IdealSheaf.Quotient.sheaf (subobject π) ≅ Q :=
  @asIso _ _ _ _ (quotientComparison π) h

/-- The forward map of `quotientIso π h` is the canonical quotient comparison. -/
@[simp, stacks 0B8S "quotient comparison isomorphism forward map"]
theorem quotientIso_hom (π : A ⟶ Q) (h : IsIso (quotientComparison π)) :
    (quotientIso π h).hom = quotientComparison π := sorry

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

end LocalComparison

end SheafOfModules.RingedSite.KernelIdeal
