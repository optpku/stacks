/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.Tactic.CrossRefAttribute

/-!
# Pushouts of modules as quotients

@stack 00D8
@stack 0AUM

For linear maps `f : M -> N` and `g : M -> P`, this file realizes their pushout as the quotient
of `N x P` by the range of `x |-> (f x, -g x)`.  Mathlib owns the abstract pushout and cokernel
formalism; this file supplies the concrete `ModuleCat` model and its elementwise API.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v w

namespace ModuleCat.PushoutQuotient

variable {R : Type u} [Ring R]
variable {M N P : Type v}
variable [AddCommGroup M] [Module R M]
variable [AddCommGroup N] [Module R N]
variable [AddCommGroup P] [Module R P]

/-- The relation map whose cokernel is the pushout of `f` and `g`. -/
@[stacks 00D8, stacks 0AUM "pushout difference map"]
def difference (f : M →ₗ[R] N) (g : M →ₗ[R] P) : M →ₗ[R] N × P :=
  f.prod (-g)

/-- The concrete quotient model for the pushout of two linear maps. -/
@[stacks 00D8, stacks 0AUM "explicit pushout quotient"]
abbrev quotient (f : M →ₗ[R] N) (g : M →ₗ[R] P) :=
  (N × P) ⧸ LinearMap.range (difference f g)

/-- The left structure map into the quotient pushout. -/
@[stacks 00D8 "left pushout leg"]
def inl (f : M →ₗ[R] N) (g : M →ₗ[R] P) : N →ₗ[R] quotient f g :=
  (LinearMap.range (difference f g)).mkQ.comp (LinearMap.inl R N P)

/-- The right structure map into the quotient pushout. -/
@[stacks 00D8, stacks 0AUM "right pushout leg"]
def inr (f : M →ₗ[R] N) (g : M →ₗ[R] P) : P →ₗ[R] quotient f g :=
  (LinearMap.range (difference f g)).mkQ.comp (LinearMap.inr R N P)

/-- The two quotient structure maps agree on the common source. -/
@[stacks 00D8 "pushout relation"]
theorem condition (f : M →ₗ[R] N) (g : M →ₗ[R] P) :
    (inl f g).comp f = (inr f g).comp g := by
  ext x
  change Submodule.Quotient.mk
      (((LinearMap.inl R N P).comp f) x : N × P) =
    Submodule.Quotient.mk (((LinearMap.inr R N P).comp g) x : N × P)
  exact (Submodule.Quotient.eq _).2 ⟨x, by simp [difference]⟩

section Desc

variable {Q : Type w} [AddCommGroup Q] [Module R Q]

/-- The map out of a quotient pushout induced by a compatible pair of linear maps. -/
@[stacks 00D8 "pushout desc"]
noncomputable def desc (f : M →ₗ[R] N) (g : M →ₗ[R] P)
    (β : N →ₗ[R] Q) (γ : P →ₗ[R] Q) (h : β.comp f = γ.comp g) :
    quotient f g →ₗ[R] Q :=
  (LinearMap.range (difference f g)).liftQ (LinearMap.coprod β γ) <| by
    rw [LinearMap.range_le_ker_iff]
    ext x
    have hx : β (f x) = γ (g x) := LinearMap.congr_fun h x
    simpa [difference, sub_eq_add_neg] using sub_eq_zero.mpr hx

/-- The pushout descendent restricts to its left input map. -/
@[simp, stacks 00D8 "pushout desc on the left leg"]
theorem desc_comp_inl (f : M →ₗ[R] N) (g : M →ₗ[R] P)
    (β : N →ₗ[R] Q) (γ : P →ₗ[R] Q) (h : β.comp f = γ.comp g) :
    (desc f g β γ h).comp (inl f g) = β := by
  simp [desc, inl, <- LinearMap.comp_assoc]

/-- The pushout descendent restricts to its right input map. -/
@[simp, stacks 00D8 "pushout desc on the right leg"]
theorem desc_comp_inr (f : M →ₗ[R] N) (g : M →ₗ[R] P)
    (β : N →ₗ[R] Q) (γ : P →ₗ[R] Q) (h : β.comp f = γ.comp g) :
    (desc f g β γ h).comp (inr f g) = γ := by
  simp [desc, inr, <- LinearMap.comp_assoc]

/-- Linear maps out of a quotient pushout are determined by the two structure maps. -/
@[ext, stacks 00D8 "pushout hom extensionality"]
theorem hom_ext {f : M →ₗ[R] N} {g : M →ₗ[R] P}
    {φ ψ : quotient f g →ₗ[R] Q}
    (hl : φ.comp (inl f g) = ψ.comp (inl f g))
    (hr : φ.comp (inr f g) = ψ.comp (inr f g)) : φ = ψ := by
  apply LinearMap.ext
  intro q
  refine Submodule.Quotient.induction_on (LinearMap.range (difference f g)) q ?_
  rintro ⟨n, p⟩
  have hsplit :
      (Submodule.Quotient.mk (n, p) : quotient f g) =
        Submodule.Quotient.mk (n, 0) + Submodule.Quotient.mk (0, p) := by
    simpa using
      (Submodule.Quotient.mk_add (LinearMap.range (difference f g)) :
        (Submodule.Quotient.mk
            ((((n, (0 : P)) : N × P) + (((0 : N), p) : N × P)) : N × P) :
          quotient f g) =
        Submodule.Quotient.mk ((n, (0 : P)) : N × P) +
          Submodule.Quotient.mk (((0 : N), p) : N × P))
  have hn :
      φ (Submodule.Quotient.mk (n, 0) : quotient f g) =
        ψ (Submodule.Quotient.mk (n, 0) : quotient f g) := by
    simpa [inl] using LinearMap.congr_fun hl n
  have hp :
      φ (Submodule.Quotient.mk (0, p) : quotient f g) =
        ψ (Submodule.Quotient.mk (0, p) : quotient f g) := by
    simpa [inr] using LinearMap.congr_fun hr p
  rw [hsplit, map_add, map_add, hn, hp]

end Desc

/-- The explicit quotient with its two structure maps, as a pushout cocone. -/
@[stacks 00D8 "explicit pushout cocone"]
def cocone (f : M →ₗ[R] N) (g : M →ₗ[R] P) :
    PushoutCocone (ModuleCat.ofHom f) (ModuleCat.ofHom g) :=
  PushoutCocone.mk (ModuleCat.ofHom (inl f g)) (ModuleCat.ofHom (inr f g)) <| by
    simpa [ModuleCat.ofHom_comp] using congrArg ModuleCat.ofHom (condition f g)

/-- The explicit quotient cocone satisfies the pushout universal property. -/
@[stacks 00D8, stacks 0AUM "explicit quotient is a pushout"]
noncomputable def isColimit (f : M →ₗ[R] N) (g : M →ₗ[R] P) :
    IsColimit (cocone f g) :=
  PushoutCocone.IsColimit.mk
    (by simpa [ModuleCat.ofHom_comp] using congrArg ModuleCat.ofHom (condition f g))
    (fun s => ModuleCat.ofHom <|
      desc f g s.inl.hom s.inr.hom (congrArg ModuleCat.Hom.hom s.condition))
    (fun s => ModuleCat.hom_ext <|
      desc_comp_inl f g s.inl.hom s.inr.hom (congrArg ModuleCat.Hom.hom s.condition))
    (fun s => ModuleCat.hom_ext <|
      desc_comp_inr f g s.inl.hom s.inr.hom (congrArg ModuleCat.Hom.hom s.condition))
    (fun s m hmN hmP => ModuleCat.hom_ext <| hom_ext
      (by
        have hmN' : m.hom.comp (inl f g) = s.inl.hom := by
          simpa only [ModuleCat.hom_comp, ModuleCat.hom_ofHom] using
            congrArg ModuleCat.Hom.hom hmN
        exact hmN'.trans <|
          (desc_comp_inl f g s.inl.hom s.inr.hom
            (congrArg ModuleCat.Hom.hom s.condition)).symm)
      (by
        have hmP' : m.hom.comp (inr f g) = s.inr.hom := by
          simpa only [ModuleCat.hom_comp, ModuleCat.hom_ofHom] using
            congrArg ModuleCat.Hom.hom hmP
        exact hmP'.trans <|
          (desc_comp_inr f g s.inl.hom s.inr.hom
            (congrArg ModuleCat.Hom.hom s.condition)).symm))

/-- The categorical pushout is canonically isomorphic to the explicit quotient model. -/
@[stacks 00D8, stacks 0AUM "categorical pushout quotient comparison"]
noncomputable def iso (f : M →ₗ[R] N) (g : M →ₗ[R] P) :
    pushout (ModuleCat.ofHom f) (ModuleCat.ofHom g) ≅ ModuleCat.of R (quotient f g) :=
  (pushoutIsPushout (ModuleCat.ofHom f) (ModuleCat.ofHom g)).coconePointUniqueUpToIso
    (isColimit f g)

/-- The pushout comparison carries the categorical left leg to the quotient left leg. -/
@[simp, stacks 00D8 "pushout comparison on the left leg"]
theorem inl_iso_hom (f : M →ₗ[R] N) (g : M →ₗ[R] P) :
    pushout.inl (ModuleCat.ofHom f) (ModuleCat.ofHom g) ≫ (iso f g).hom =
      ModuleCat.ofHom (inl f g) := by
  exact
    (pushoutIsPushout (ModuleCat.ofHom f) (ModuleCat.ofHom g)).comp_coconePointUniqueUpToIso_hom
      (isColimit f g) WalkingSpan.left

/-- The pushout comparison carries the categorical right leg to the quotient right leg. -/
@[simp, stacks 00D8, stacks 0AUM "pushout comparison on the right leg"]
theorem inr_iso_hom (f : M →ₗ[R] N) (g : M →ₗ[R] P) :
    pushout.inr (ModuleCat.ofHom f) (ModuleCat.ofHom g) ≫ (iso f g).hom =
      ModuleCat.ofHom (inr f g) := by
  exact
    (pushoutIsPushout (ModuleCat.ofHom f) (ModuleCat.ofHom g)).comp_coconePointUniqueUpToIso_hom
      (isColimit f g) WalkingSpan.right

/-- Linear-map form of the left-leg compatibility. -/
@[simp]
theorem iso_hom_comp_inl (f : M →ₗ[R] N) (g : M →ₗ[R] P) :
    (iso f g).hom.hom.comp
        (pushout.inl (ModuleCat.ofHom f) (ModuleCat.ofHom g)).hom = inl f g := by
  simpa only [ModuleCat.hom_comp, ModuleCat.hom_ofHom] using
    congrArg ModuleCat.Hom.hom (inl_iso_hom f g)

/-- Linear-map form of the right-leg compatibility. -/
@[simp]
theorem iso_hom_comp_inr (f : M →ₗ[R] N) (g : M →ₗ[R] P) :
    (iso f g).hom.hom.comp
        (pushout.inr (ModuleCat.ofHom f) (ModuleCat.ofHom g)).hom = inr f g := by
  simpa only [ModuleCat.hom_comp, ModuleCat.hom_ofHom] using
    congrArg ModuleCat.Hom.hom (inr_iso_hom f g)

/-- The kernel of the left pushout leg is the image under `f` of the kernel of `g`. -/
@[stacks 00D8 "kernel of the left pushout leg"]
theorem ker_inl (f : M →ₗ[R] N) (g : M →ₗ[R] P) :
    LinearMap.ker (inl f g) = Submodule.map f (LinearMap.ker g) := sorry

/-- The kernel of the right pushout leg is the image under `g` of the kernel of `f`. -/
@[stacks 00D8, stacks 0AUM "kernel of the right pushout leg"]
theorem ker_inr (f : M →ₗ[R] N) (g : M →ₗ[R] P) :
    LinearMap.ker (inr f g) = Submodule.map g (LinearMap.ker f) := sorry

/-- The common source map to the pushout has kernel `ker f sup ker g`. -/
@[stacks 00D8 "kernel of the source map to a pushout"]
theorem ker_inl_comp (f : M →ₗ[R] N) (g : M →ₗ[R] P) :
    LinearMap.ker ((inl f g).comp f) = LinearMap.ker f ⊔ LinearMap.ker g := sorry

/-- Symmetric form of `ker_inl_comp` using the right structure map. -/
@[stacks 00D8 "kernel of the source map through the right pushout leg"]
theorem ker_inr_comp (f : M →ₗ[R] N) (g : M →ₗ[R] P) :
    LinearMap.ker ((inr f g).comp g) = LinearMap.ker f ⊔ LinearMap.ker g := by
  rw [← condition f g]
  exact ker_inl_comp f g

/-- Example 10.8.5 (Tag `00D8`): if the image under the left map of the kernel of the right map
is nonzero, then an element dies in the pushout although it does not die at any later vertex of
the walking-span diagram. This is the direct failure of the eventual-vanishing conclusion without
directedness. -/
@[stacks 00D8 "failure of eventual vanishing without directedness"]
theorem exists_inl_eq_zero_not_eventually_zero
    (f : M →ₗ[R] N) (g : M →ₗ[R] P)
    (hker : Submodule.map f (LinearMap.ker g) ≠ ⊥) :
    ∃ x : N,
      inl f g x = 0 ∧
        ¬ ∃ j : WalkingSpan, ∃ h : WalkingSpan.left ⟶ j,
          ((span (ModuleCat.ofHom f) (ModuleCat.ofHom g)).map h).hom x = 0 := sorry

end ModuleCat.PushoutQuotient
