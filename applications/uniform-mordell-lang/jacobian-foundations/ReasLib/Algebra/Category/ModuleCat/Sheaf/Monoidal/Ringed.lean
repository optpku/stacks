module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Localization
public import Mathlib.CategoryTheory.Localization.Monoidal.Braided
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.PresheafMonoidal
public import Mathlib.Tactic.CrossRefAttribute

/-!
# The symmetric monoidal category of modules on a commutative ringed site

Module sheafification is a localization of the pointwise symmetric monoidal category of module
presheaves.  This file records the compatibility of its weak equivalences with tensor products
and uses Mathlib's monoidal-localization construction to put the canonical symmetric monoidal
structure on module sheaves.
-/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory

noncomputable section

universe u v w

namespace SheafOfModules.RingedSite

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable [HasWeakSheafify J AddCommGrpCat.{w}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable (O : Sheaf J CommRingCat.{w})

namespace Tensor

/-- The morphisms of module presheaves that are locally bijective after forgetting the module
structure. -/
@[stacks 0GMW "weak equivalences for module sheafification"]
abbrev weakEquivalences :
    MorphismProperty (PresheafOfModules.{w} (ringSheaf J O).obj) :=
  J.W.inverseImage (PresheafOfModules.toPresheaf (ringSheaf J O).obj)

/-- The tensor product of two locally bijective module-presheaf morphisms is locally bijective.
This is the mathematical closure statement needed by monoidal localization; exposing it separately
keeps proofs and downstream uses independent of the packaging as an `IsMonoidal` instance. -/
@[stacks 0GMW "tensor stability of locally bijective module-presheaf morphisms"]
theorem weakEquivalences_tensorHom
    {F₁ F₂ G₁ G₂ : PresheafOfModules.{w} (ringSheaf J O).obj}
    (f : F₁ ⟶ F₂) (g : G₁ ⟶ G₂)
    (hf : weakEquivalences O f) (hg : weakEquivalences O g) :
    weakEquivalences O (f ⊗ₘ g) := sorry

/-- Locally bijective module-presheaf morphisms form a monoidal morphism property. -/
@[stacks 0GMW "monoidal weak equivalences for module sheafification"]
instance weakEquivalences.isMonoidal :
    (weakEquivalences O).IsMonoidal :=
  MorphismProperty.IsMonoidal.mk' _ (weakEquivalences_tensorHom O)

/-- The monoidal structure on module sheaves obtained from the monoidal localization of module
presheaves. -/
@[stacks 0GMW "monoidal localization presentation of module sheaves", reducible]
noncomputable def monoidalCategory
    : MonoidalCategory (ringedSiteModuleCategory.{u, v, w, w} J O) :=
  inferInstanceAs <| MonoidalCategory <|
    LocalizedMonoidal
      (PresheafOfModules.sheafification (𝟙 (ringSheaf J O).obj))
      (weakEquivalences O) (Iso.refl _)

end Tensor

/-- The canonical monoidal structure on modules over a commutative ring sheaf. -/
@[stacks 0GMW "canonical monoidal structure on module sheaves", reducible]
noncomputable instance moduleMonoidalCategory
    : MonoidalCategory (ringedSiteModuleCategory.{u, v, w, w} J O) :=
  Tensor.monoidalCategory O

namespace Tensor

/-- Module sheafification is monoidal for the canonical localization monoidal structures. -/
@[stacks 0GMW "module sheafification is monoidal"]
noncomputable instance sheafificationMonoidal
    : (PresheafOfModules.sheafification
      (𝟙 (ringSheaf J O).obj)).Monoidal :=
  inferInstanceAs <|
    (Localization.Monoidal.toMonoidalCategory
      (PresheafOfModules.sheafification (𝟙 (ringSheaf J O).obj))
      (weakEquivalences O) (Iso.refl _)).Monoidal

/-- The symmetric structure on module sheaves obtained from the symmetric monoidal localization
of module presheaves. -/
@[stacks 0GMW "canonical tensor product on module sheaves", reducible]
noncomputable def symmetricCategory
    : SymmetricCategory (ringedSiteModuleCategory.{u, v, w, w} J O) :=
  inferInstanceAs <| SymmetricCategory <|
    LocalizedMonoidal
      (PresheafOfModules.sheafification (𝟙 (ringSheaf J O).obj))
      (weakEquivalences O) (Iso.refl _)

end Tensor

/-- The canonical symmetry on modules over a commutative ring sheaf. -/
@[stacks 0GMW "canonical symmetry on module sheaves", reducible]
noncomputable instance moduleSymmetricCategory
    : SymmetricCategory (ringedSiteModuleCategory.{u, v, w, w} J O) :=
  Tensor.symmetricCategory O

namespace ModuleOver

/-- The canonical monoidal structure on the direct `over` presentation of a restricted module
sheaf category.  This bridge lets typeclass search pass from the underlying ring-sheaf
presentation back to the commutative ring sheaf `O.over U`. -/
@[stacks 0GMW "canonical tensor product on a slice site"]
noncomputable instance monoidalCategory (U : C)
    [(J.over U).HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    [HasWeakSheafify (J.over U) AddCommGrpCat.{w}]
    [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{w}] :
    MonoidalCategory (SheafOfModules.{w} ((ringSheaf J O).over U)) :=
  moduleMonoidalCategory (J := J.over U) (O.over U)

/-- The canonical symmetry on the direct `over` presentation of a restricted module sheaf
category. -/
@[stacks 0GMW "canonical symmetry on a slice site"]
noncomputable instance symmetricCategory (U : C)
    [(J.over U).HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    [HasWeakSheafify (J.over U) AddCommGrpCat.{w}]
    [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{w}] :
    SymmetricCategory (SheafOfModules.{w} ((ringSheaf J O).over U)) :=
  moduleSymmetricCategory (J := J.over U) (O.over U)

end ModuleOver

end SheafOfModules.RingedSite
