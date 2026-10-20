/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.Algebra.Group.Submonoid.Divisibility
public import ReasLib.Algebra.Module.LocalizedModule.Away.Map

/-!
# Principal Localizations Indexed by Divisibility

This leaf records the diagram of principal localizations indexed by the
divisibility preorder on a submonoid and its canonical cocone into the total
localization.

The descent morphism below is concrete; only its well-definedness, linearity, and universal
property laws are deferred as proposition-valued statements.

@stack 00CR
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace LocalizedModule.Away

variable {R : Type u} [CommRing R]

/-- Tag `00CR`: the `ModuleCat R` morphism between principal localizations
induced by a divisibility relation inside a submonoid. -/
@[stacks 00CR "principal localized module divisibility morphism"]
noncomputable def divisibilityMap
    (S : Submonoid R) (M : Type v) [AddCommGroup M] [Module R M]
    {a b : S.Divisibility} (h : a ≤ b) :
    ModuleCat.of R (LocalizedModule.Away (a : R) M) ⟶
      ModuleCat.of R (LocalizedModule.Away (b : R) M) :=
  ModuleCat.ofHom (mapOfDvd (M := M) (a : R) (b : R) h)

/-- The divisibility morphism at an identity relation is the identity module
morphism. -/
@[simp, stacks 00CR "principal localized module divisibility identity"]
theorem divisibilityMap_id
    (S : Submonoid R) (M : Type v) [AddCommGroup M] [Module R M]
    (s : S.Divisibility) :
    divisibilityMap S M (leOfHom (𝟙 s)) = 𝟙 _ := sorry

/-- Divisibility morphisms between principal localizations compose along
composition in the divisibility preorder. -/
@[stacks 00CR "principal localized module divisibility composition"]
theorem divisibilityMap_comp
    (S : Submonoid R) (M : Type v) [AddCommGroup M] [Module R M]
    {a b c : S.Divisibility} (f : a ⟶ b) (g : b ⟶ c) :
    divisibilityMap S M (leOfHom (f ≫ g)) =
      divisibilityMap S M (leOfHom f) ≫ divisibilityMap S M (leOfHom g) := sorry

/-- Tag `00CR`: the diagram of principal localizations of `M` indexed by
elements of `S` ordered by divisibility. -/
@[stacks 00CR "principal localized module divisibility diagram"]
noncomputable def divisibilityDiagram
    (S : Submonoid R) (M : Type v) [AddCommGroup M] [Module R M] :
    S.Divisibility ⥤ ModuleCat R where
  obj s := ModuleCat.of R (LocalizedModule.Away (s : R) M)
  map f := divisibilityMap S M (leOfHom f)
  map_id := fun s ↦ divisibilityMap_id S M s
  map_comp := fun f g ↦ divisibilityMap_comp S M f g

/-- Canonical maps from principal localizations to the total localization are
natural along a divisibility morphism. -/
@[stacks 00CR "principal localized module divisibility cocone naturality"]
theorem divisibilityCocone_naturality
    (S : Submonoid R) (M : Type v) [AddCommGroup M] [Module R M]
    {a b : S.Divisibility} (f : a ⟶ b) :
    divisibilityMap S M (leOfHom f) ≫
        ModuleCat.ofHom (toLocalizedModule (M := M) S (b : S)) =
      ModuleCat.ofHom (toLocalizedModule (M := M) S (a : S)) := sorry

/-- Tag `00CR`: the canonical cocone from the divisibility diagram of
principal localizations to the total localization at `S`. -/
@[stacks 00CR "principal localized module divisibility cocone"]
noncomputable def divisibilityCocone
    (S : Submonoid R) (M : Type v) [AddCommGroup M] [Module R M] :
    Cocone (divisibilityDiagram S M) where
  pt := ModuleCat.of R (LocalizedModule S M)
  ι :=
    { app := fun s ↦ ModuleCat.ofHom (toLocalizedModule (M := M) S (s : S))
      naturality := fun _ _ f ↦ divisibilityCocone_naturality S M f }

namespace divisibilityCoconeDesc

/-- Evaluating a cocone in the denominator component respects the equivalence relation defining
the total localized module. -/
@[stacks 00CR "principal localization cocone descent well-definedness"]
theorem wellDefined
    (S : Submonoid R) (M : Type v) [AddCommGroup M] [Module R M]
    (c : Cocone (divisibilityDiagram S M)) (p p' : M × S) (h : p ≈ p') :
    c.ι.app p.2 (LocalizedModule.mk p.1 (Submonoid.pow (p.2 : R) 1)) =
      c.ι.app p'.2 (LocalizedModule.mk p'.1 (Submonoid.pow (p'.2 : R) 1)) := sorry

/-- The underlying function of the canonical descent morphism evaluates a fraction in the cocone
component indexed by its denominator. -/
@[stacks 00CR "principal localization cocone descent function"]
noncomputable def toFun
    (S : Submonoid R) (M : Type v) [AddCommGroup M] [Module R M]
    (c : Cocone (divisibilityDiagram S M)) : LocalizedModule S M → c.pt :=
  fun x ↦ x.liftOn
    (fun p ↦ c.ι.app p.2 (LocalizedModule.mk p.1 (Submonoid.pow (p.2 : R) 1)))
    (wellDefined S M c)

/-- The underlying descent function preserves addition. -/
@[stacks 00CR "principal localization cocone descent additivity"]
theorem map_add
    (S : Submonoid R) (M : Type v) [AddCommGroup M] [Module R M]
    (c : Cocone (divisibilityDiagram S M)) (x y : LocalizedModule S M) :
    toFun S M c (x + y) = toFun S M c x + toFun S M c y := sorry

/-- The underlying descent function preserves scalar multiplication. -/
@[stacks 00CR "principal localization cocone descent scalar action"]
theorem map_smul
    (S : Submonoid R) (M : Type v) [AddCommGroup M] [Module R M]
    (c : Cocone (divisibilityDiagram S M)) (r : R) (x : LocalizedModule S M) :
    toFun S M c (r • x) = r • toFun S M c x := sorry

end divisibilityCoconeDesc

/-- The canonical descent morphism from the total localization to the vertex of a cocone on the
principal-localization diagram. -/
@[stacks 00CR "principal localization cocone descent"]
noncomputable def divisibilityCoconeDesc
    (S : Submonoid R) (M : Type v) [AddCommGroup M] [Module R M]
    (c : Cocone (divisibilityDiagram S M)) :
    (divisibilityCocone S M).pt ⟶ c.pt :=
  ModuleCat.ofHom
    { toFun := divisibilityCoconeDesc.toFun S M c
      map_add' := divisibilityCoconeDesc.map_add S M c
      map_smul' := divisibilityCoconeDesc.map_smul S M c }

/-- The canonical descent morphism evaluates a localized fraction in the component indexed by its
denominator. -/
@[simp, stacks 00CR "principal localization cocone descent application"]
theorem divisibilityCoconeDesc_apply_mk
    (S : Submonoid R) (M : Type v) [AddCommGroup M] [Module R M]
    (c : Cocone (divisibilityDiagram S M)) (m : M) (s : S) :
    divisibilityCoconeDesc S M c (LocalizedModule.mk m s) =
      c.ι.app s (LocalizedModule.mk m (Submonoid.pow (s : R) 1)) := sorry

/-- The canonical descent morphism factors every leg of the total-localization cocone. -/
@[reassoc, simp, stacks 00CR "principal localization cocone descent factorization"]
theorem divisibilityCoconeDesc_fac
    (S : Submonoid R) (M : Type v) [AddCommGroup M] [Module R M]
    (c : Cocone (divisibilityDiagram S M)) (s : S.Divisibility) :
    (divisibilityCocone S M).ι.app s ≫ divisibilityCoconeDesc S M c = c.ι.app s := sorry

/-- A morphism compatible with all principal-localization cocone legs is the canonical descent
morphism. -/
@[stacks 00CR "principal localization cocone descent uniqueness"]
theorem divisibilityCoconeDesc_unique
    (S : Submonoid R) (M : Type v) [AddCommGroup M] [Module R M]
    (c : Cocone (divisibilityDiagram S M))
    (t : (divisibilityCocone S M).pt ⟶ c.pt)
    (ht : ∀ s : S.Divisibility, (divisibilityCocone S M).ι.app s ≫ t = c.ι.app s) :
    t = divisibilityCoconeDesc S M c := sorry

/-- Tag `00CR`: every cocone on principal localizations indexed by
divisibility admits a unique compatible morphism from the total localization.
This is the universal-property form suitable for the statement stage. -/
@[stacks 00CR "principal localized module divisibility universal property"]
theorem divisibilityCocone_existsUniqueDesc
    (S : Submonoid R) (M : Type v) [AddCommGroup M] [Module R M]
    (c : Cocone (divisibilityDiagram S M)) :
    ∃! t : (divisibilityCocone S M).pt ⟶ c.pt,
      ∀ s : S.Divisibility, (divisibilityCocone S M).ι.app s ≫ t = c.ι.app s := sorry

/-- Lemma 10.9.9: the total localization is the colimit of the principal-localization diagram.

The `IsColimit` owner is kept beside the diagram and cocone so downstream users can consume one
canonical object instead of rebuilding a source-specific descent proof. -/
@[stacks 00CR "principal localization colimit"]
noncomputable def divisibilityCocone_isColimit
    (S : Submonoid R) (M : Type v) [AddCommGroup M] [Module R M] :
    IsColimit (divisibilityCocone S M) where
  desc := divisibilityCoconeDesc S M
  fac := divisibilityCoconeDesc_fac S M
  uniq := divisibilityCoconeDesc_unique S M

/-- The colimit comparison map restricts to each cocone leg. -/
@[reassoc, simp, stacks 00CR "principal localization colimit factorization"]
theorem divisibilityCocone_isColimit_fac
    (S : Submonoid R) (M : Type v) [AddCommGroup M] [Module R M]
    (c : Cocone (divisibilityDiagram S M)) (s : S.Divisibility) :
    (divisibilityCocone S M).ι.app s ≫
        (divisibilityCocone_isColimit S M).desc c = c.ι.app s := sorry

end LocalizedModule.Away
