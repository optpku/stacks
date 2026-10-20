/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.Ring.Constructions
public import Mathlib.CategoryTheory.Sites.Limits
public import Mathlib.CategoryTheory.Sites.Over
import Mathlib.Tactic.CrossRefAttribute

/-!
# Locally finite products of commutative-ring sheaves

This file packages the site-theoretic infrastructure behind decompositions of a commutative-ring
sheaf as a locally finite product.  Triviality is expressed categorically by terminality: the
category of commutative rings has a terminal trivial ring but no zero object.
-/

@[expose] public section

open CategoryTheory.Limits Opposite

noncomputable section

universe u v w uι uκ

namespace CategoryTheory.Sheaf

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

/-- A commutative-ring-valued sheaf is trivial when it is terminal in the sheaf category. -/
@[stacks 0FPG "trivial factor sheaf", stacks 0FPY "trivial factor sheaf"]
def IsTrivialRing (F : Sheaf J CommRingCat.{w}) : Prop :=
  Nonempty (IsTerminal F)

/-- A commutative-ring-valued sheaf is trivial exactly when every ring of sections is
subsingleton. -/
theorem isTrivialRing_iff_obj_subsingleton (F : Sheaf J CommRingCat.{w}) :
    IsTrivialRing F ↔ ∀ U : C, Subsingleton (F.obj.obj (op U)) := sorry

/-- Every ring of sections of a trivial commutative-ring-valued sheaf is subsingleton. -/
theorem IsTrivialRing.obj_subsingleton {F : Sheaf J CommRingCat.{w}}
    (hF : IsTrivialRing F) (U : C) :
    Subsingleton (F.obj.obj (op U)) := sorry

/-- Triviality of commutative-ring-valued sheaves is invariant under isomorphism. -/
theorem isTrivialRing_iff_of_iso {F G : Sheaf J CommRingCat.{w}} (e : F ≅ G) :
    IsTrivialRing F ↔ IsTrivialRing G := sorry

/-- Transport triviality of a commutative-ring-valued sheaf across an isomorphism. -/
theorem IsTrivialRing.of_iso {F G : Sheaf J CommRingCat.{w}}
    (hF : IsTrivialRing F) (e : F ≅ G) :
    IsTrivialRing G := sorry

namespace RingFamily

variable {ι : Type uι}

/-- The support of a family of commutative-ring-valued sheaves after restriction to the slice
site over `U`. -/
def supportOver (F : ι → Sheaf J CommRingCat.{w}) (U : C) : Set ι :=
  {i | ¬ IsTrivialRing ((F i).over U)}

/-- Membership in `supportOver F U` means that the corresponding factor remains nontrivial on
the slice site over `U`. -/
@[simp]
theorem mem_supportOver_iff (F : ι → Sheaf J CommRingCat.{w}) (U : C) (i : ι) :
    i ∈ supportOver F U ↔ ¬ IsTrivialRing ((F i).over U) := sorry

/-- A family of commutative-ring-valued sheaves is locally finite when every object of the site
has a covering on whose members only finitely many restricted factors are nontrivial. -/
@[stacks 0FPG "locally finite family of factor sheaves",
  stacks 0FPY "locally finite family of factor sheaves"]
def IsLocallyFinite (F : ι → Sheaf J CommRingCat.{w}) : Prop :=
  ∀ U : C, ∃ T : J.Cover U, ∀ a : T.Arrow, (supportOver F a.Y).Finite

/-- The covering formulation is the defining criterion for a locally finite family of
commutative-ring-valued sheaves. -/
theorem isLocallyFinite_iff (F : ι → Sheaf J CommRingCat.{w}) :
    IsLocallyFinite F ↔
      ∀ U : C, ∃ T : J.Cover U, ∀ a : T.Arrow, (supportOver F a.Y).Finite := sorry

/-- Extract a cover on which the support of a locally finite family is finite. -/
theorem IsLocallyFinite.exists_cover {F : ι → Sheaf J CommRingCat.{w}}
    (hF : IsLocallyFinite F) (U : C) :
    ∃ T : J.Cover U, ∀ a : T.Arrow, (supportOver F a.Y).Finite := sorry

/-- Reindexing a restricted support along an equivalence takes its inverse image. -/
@[simp]
theorem supportOver_reindex {κ : Type uκ} (F : ι → Sheaf J CommRingCat.{w})
    (e : κ ≃ ι) (U : C) :
    supportOver (F ∘ e) U = e ⁻¹' supportOver F U := sorry

/-- A locally finite family remains locally finite after reindexing by an equivalence. -/
theorem IsLocallyFinite.reindex {κ : Type uκ} {F : ι → Sheaf J CommRingCat.{w}}
    (hF : IsLocallyFinite F) (e : κ ≃ ι) :
    IsLocallyFinite (F ∘ e) := sorry

/-- Restricting a locally finite family to a slice site preserves local finiteness. -/
theorem IsLocallyFinite.over {F : ι → Sheaf J CommRingCat.{w}}
    (hF : IsLocallyFinite F) (U : C) :
    IsLocallyFinite (J := J.over U) (fun i ↦ (F i).over U) := sorry

end RingFamily

/-- A specified product decomposition of a commutative-ring-valued sheaf whose family of
factors is locally finite on the site. -/
@[stacks 0FPG "locally finite product decomposition of a ring sheaf",
  stacks 0FPY "locally finite product decomposition of a ring sheaf"]
structure LocallyFiniteProduct
    (O : Sheaf J CommRingCat.{w}) (ι : Type uι) [Small.{w} ι] where
  /-- The indexed family of factor sheaves. -/
  factor : ι → Sheaf J CommRingCat.{w}
  /-- The specified identification of the original sheaf with the categorical product of the
  factor sheaves. -/
  productIso : O ≅ ∏ᶜ factor
  /-- The factor family is locally finite. -/
  localFinite : RingFamily.IsLocallyFinite factor

namespace LocallyFiniteProduct

variable {ι : Type uι} [Small.{w} ι]
variable {O : Sheaf J CommRingCat.{w}}

/-- The projection from a locally finite product decomposition to one of its factor sheaves. -/
def π (D : LocallyFiniteProduct O ι) (i : ι) : O ⟶ D.factor i :=
  D.productIso.hom ≫ Limits.Pi.π D.factor i

/-- The projection of a locally finite product is the product isomorphism followed by the
categorical product projection. -/
@[simp]
theorem π_eq (D : LocallyFiniteProduct O ι) (i : ι) :
    D.π i = D.productIso.hom ≫ Limits.Pi.π D.factor i := sorry

/-- Extract a cover on whose members only finitely many factors of a locally finite product are
nontrivial. -/
theorem exists_cover (D : LocallyFiniteProduct O ι) (U : C) :
    ∃ T : J.Cover U, ∀ a : T.Arrow,
      (RingFamily.supportOver D.factor a.Y).Finite := sorry

/-- Reindex a locally finite product decomposition by an equivalence of index types. -/
def reindex {κ : Type uκ} [Small.{w} κ]
    (D : LocallyFiniteProduct O ι) (e : κ ≃ ι) :
    LocallyFiniteProduct O κ where
  factor := D.factor ∘ e
  productIso := D.productIso ≪≫ (Limits.Pi.reindex e D.factor).symm
  localFinite := D.localFinite.reindex e

/-- Reindexing a locally finite product carries each projection to the corresponding original
projection. -/
@[simp]
theorem reindex_π {κ : Type uκ} [Small.{w} κ]
    (D : LocallyFiniteProduct O ι) (e : κ ≃ ι) (k : κ) :
    (D.reindex e).π k = D.π (e k) := sorry

end LocallyFiniteProduct

end CategoryTheory.Sheaf
