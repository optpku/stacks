module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pullback
public import Mathlib.CategoryTheory.Functor.Flat
public import ReasLib.Algebra.Category.ModuleCat.Presheaf.Tensor.Pushforward
public import ReasLib.CategoryTheory.Iso.Explicit
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Monoidal pullback for presheaves of modules

Restriction of scalars is lax monoidal, so its left adjoint carries a canonical oplax
comparison. Representable flatness makes the unit and tensor comparisons invertible. The
forward comparison morphisms and the constructions from explicit invertibility certificates
are both named here.
-/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory
open CategoryTheory.Functor.OplaxMonoidal

noncomputable section

universe u uC vC uD vD

namespace PresheafOfModules.Pullback

variable {C : Type uC} [Category.{vC} C]
variable {D : Type uD} [Category.{vD} D]
variable (F : C ⥤ D)
variable {O : Cᵒᵖ ⥤ CommRingCat.{u}} {O' : Dᵒᵖ ⥤ CommRingCat.{u}}
variable (b : O ⟶ F.op ⋙ O')

/-- The underlying morphism of ring presheaves used by module pullback. -/
@[stacks 03EL "underlying ring presheaf map"]
abbrev ringMap : ringPresheaf O ⟶ F.op ⋙ ringPresheaf O' :=
  PresheafOfModules.Pushforward.ringMap F b

variable [(PresheafOfModules.pushforward.{u} (ringMap F b)).IsRightAdjoint]

/-- Pullback of module presheaves carries the oplax structure transported across its
pullback-pushforward adjunction. -/
@[stacks 03EL "module-presheaf pullback oplax structure", implicit_reducible]
noncomputable instance pullbackOplaxMonoidal :
    (PresheafOfModules.pullback.{u} (ringMap F b)).OplaxMonoidal :=
  (PresheafOfModules.pullbackPushforwardAdjunction.{u}
    (ringMap F b)).leftAdjointOplaxMonoidal

/-- The canonical unit comparison for pullback of module presheaves. -/
@[stacks 03EL "module-presheaf pullback unit comparison"]
noncomputable abbrev unitComparison :
    (PresheafOfModules.pullback.{u} (ringMap F b)).obj
        (𝟙_ (PresheafOfModules.{u} (ringPresheaf O))) ⟶
      𝟙_ (PresheafOfModules.{u} (ringPresheaf O')) :=
  η (PresheafOfModules.pullback.{u} (ringMap F b))

/-- The pullback unit comparison is the adjunction transpose of the pushforward unit
comparison. -/
@[stacks 03EL "module-presheaf pullback unit comparison transpose"]
theorem unitComparison_eq :
    unitComparison F b =
      ((PresheafOfModules.pullbackPushforwardAdjunction.{u} (ringMap F b)).homEquiv _ _).symm
        (PresheafOfModules.Pushforward.unitComparison F b) := sorry

/-- The canonical tensor comparison for pullback of module presheaves. -/
@[stacks 03EL "module-presheaf pullback tensor comparison"]
noncomputable abbrev tensorComparison
    (M N : PresheafOfModules.{u} (ringPresheaf O)) :
    (PresheafOfModules.pullback.{u} (ringMap F b)).obj (M ⊗ N) ⟶
      ((PresheafOfModules.pullback.{u} (ringMap F b)).obj M ⊗
        (PresheafOfModules.pullback.{u} (ringMap F b)).obj N) :=
  δ (PresheafOfModules.pullback.{u} (ringMap F b)) M N

/-- The pullback tensor comparison is the adjunction transpose of the tensor of the two
adjunction units followed by the pushforward tensor comparison. -/
@[stacks 03EL "module-presheaf pullback tensor comparison transpose"]
theorem tensorComparison_eq
    (M N : PresheafOfModules.{u} (ringPresheaf O)) :
    tensorComparison F b M N =
      ((PresheafOfModules.pullbackPushforwardAdjunction.{u} (ringMap F b)).homEquiv _ _).symm
        (((PresheafOfModules.pullbackPushforwardAdjunction.{u}
            (ringMap F b)).unit.app M ⊗ₘ
          (PresheafOfModules.pullbackPushforwardAdjunction.{u}
            (ringMap F b)).unit.app N) ≫
          PresheafOfModules.Pushforward.tensorComparison F b
            ((PresheafOfModules.pullback.{u} (ringMap F b)).obj M)
            ((PresheafOfModules.pullback.{u} (ringMap F b)).obj N)) := sorry

/-- Upgrade the unit comparison to an isomorphism from an explicit invertibility certificate. -/
@[stacks 03EL "module-presheaf pullback unit comparison isomorphism"]
noncomputable def unitIsoOf (hη : IsIso (unitComparison F b)) :
    (PresheafOfModules.pullback.{u} (ringMap F b)).obj
        (𝟙_ (PresheafOfModules.{u} (ringPresheaf O))) ≅
      𝟙_ (PresheafOfModules.{u} (ringPresheaf O')) :=
  hη.toIso

/-- The forward map of `unitIsoOf` is the original unit comparison. -/
@[simp, stacks 03EL "explicit unit isomorphism forward map"]
theorem unitIsoOf_hom (hη : IsIso (unitComparison F b)) :
    (unitIsoOf F b hη).hom = unitComparison F b := sorry

/-- Upgrade a tensor comparison to an isomorphism from an explicit invertibility certificate. -/
@[stacks 03EL "module-presheaf pullback tensor comparison isomorphism"]
noncomputable def tensorIsoOf
    (M N : PresheafOfModules.{u} (ringPresheaf O))
    (hδ : IsIso (tensorComparison F b M N)) :
    (PresheafOfModules.pullback.{u} (ringMap F b)).obj (M ⊗ N) ≅
      ((PresheafOfModules.pullback.{u} (ringMap F b)).obj M ⊗
        (PresheafOfModules.pullback.{u} (ringMap F b)).obj N) :=
  hδ.toIso

/-- The forward map of `tensorIsoOf` is the original tensor comparison. -/
@[simp, stacks 03EL "explicit tensor isomorphism forward map"]
theorem tensorIsoOf_hom
    (M N : PresheafOfModules.{u} (ringPresheaf O))
    (hδ : IsIso (tensorComparison F b M N)) :
    (tensorIsoOf F b M N hδ).hom = tensorComparison F b M N := sorry

/-- Build the strong-monoidal core from explicit unit and tensor invertibility certificates. -/
@[stacks 03EL "explicit monoidal core for module-presheaf pullback"]
noncomputable def pullbackCoreMonoidalOf
    (hη : IsIso (unitComparison F b))
    (hδ : ∀ M N : PresheafOfModules.{u} (ringPresheaf O),
      IsIso (tensorComparison F b M N)) :
    (PresheafOfModules.pullback.{u} (ringMap F b)).CoreMonoidal :=
  -- Local instance justification (noncanonical choice): the explicit supplied unit certificate is consumed by the core constructor.
  letI : IsIso (unitComparison F b) := hη
  -- Local instance justification (noncanonical choice): the explicit supplied tensor certificates are consumed by the core constructor.
  letI : ∀ M N : PresheafOfModules.{u} (ringPresheaf O),
      IsIso (tensorComparison F b M N) := hδ
  Functor.CoreMonoidal.ofOplaxMonoidal _

/-- The class-shaped strong-monoidal view of `pullbackCoreMonoidalOf`. -/
@[stacks 03EL "explicit monoidal structure for module-presheaf pullback", implicit_reducible]
noncomputable def pullbackMonoidalOf
    (hη : IsIso (unitComparison F b))
    (hδ : ∀ M N : PresheafOfModules.{u} (ringPresheaf O),
      IsIso (tensorComparison F b M N)) :
    (PresheafOfModules.pullback.{u} (ringMap F b)).Monoidal :=
  (pullbackCoreMonoidalOf F b hη hδ).toMonoidal

variable [RepresentablyFlat F]

/-- The unit comparison for representably flat pullback of module presheaves is invertible. -/
@[stacks 03EL "module-presheaf pullback unit comparison invertibility"]
instance pullbackUnitComparison_isIso :
    IsIso (unitComparison F b) := sorry

/-- The tensor comparison for representably flat pullback of module presheaves is invertible. -/
@[stacks 03EL "module-presheaf pullback tensor comparison invertibility"]
instance pullbackTensorComparison_isIso
    (M N : PresheafOfModules.{u} (ringPresheaf O)) :
    IsIso (tensorComparison F b M N) := sorry

/-- Representably flat pullback of module presheaves is strong monoidal. -/
@[stacks 03EL "representably flat module-presheaf pullback", implicit_reducible]
noncomputable instance pullbackMonoidal :
    (PresheafOfModules.pullback.{u} (ringMap F b)).Monoidal :=
  pullbackMonoidalOf F b (pullbackUnitComparison_isIso F b)
    (fun M N ↦ pullbackTensorComparison_isIso F b M N)

/-- The unit isomorphism for representably flat pullback of module presheaves. -/
@[stacks 03EL "module-presheaf pullback unit isomorphism"]
noncomputable abbrev unitIso :
    (PresheafOfModules.pullback.{u} (ringMap F b)).obj
        (𝟙_ (PresheafOfModules.{u} (ringPresheaf O))) ≅
      𝟙_ (PresheafOfModules.{u} (ringPresheaf O')) :=
  unitIsoOf F b (pullbackUnitComparison_isIso F b)

/-- The tensor isomorphism for representably flat pullback of module presheaves. -/
@[stacks 03EL "module-presheaf pullback-tensor comparison"]
noncomputable abbrev tensorIso
    (M N : PresheafOfModules.{u} (ringPresheaf O)) :
    (PresheafOfModules.pullback.{u} (ringMap F b)).obj (M ⊗ N) ≅
      ((PresheafOfModules.pullback.{u} (ringMap F b)).obj M ⊗
        (PresheafOfModules.pullback.{u} (ringMap F b)).obj N) :=
  tensorIsoOf F b M N (pullbackTensorComparison_isIso F b M N)

end PresheafOfModules.Pullback
