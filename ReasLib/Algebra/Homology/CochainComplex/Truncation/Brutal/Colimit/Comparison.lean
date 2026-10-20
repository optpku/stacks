/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.Truncation.Brutal.Trunc.Colimit
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Comparison with Chosen Colimits of Brutal Truncations

This leaf compares Mathlib's chosen colimit with the canonical colimit cocone
owned by `Brutal.Trunc`.  The comparison isomorphism is obtained directly from
the two universal properties; it is not produced by choosing an inverse to a
deferred `IsIso` proof.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe v u

namespace CategoryTheory.CochainComplex.Brutal.Trunc.Colimit

variable {A : Type u} [Category.{v} A] [Abelian A]

/-- The chosen colimit of a brutal truncation diagram is canonically
isomorphic to the original complex. -/
@[stacks 0D8Z]
noncomputable def comparisonIso (K : CochainComplex A ℤ)
    [HasColimit (Trunc.diagram K)] : colimit (Trunc.diagram K) ≅ K :=
  Limits.colimit.isoColimitCocone (Trunc.colimitCocone K)

/-- The canonical comparison from a chosen colimit of the brutal truncation
diagram to the original complex. -/
@[stacks 0D8Z]
noncomputable abbrev comparison (K : CochainComplex A ℤ)
    [HasColimit (Trunc.diagram K)] : colimit (Trunc.diagram K) ⟶ K :=
  (comparisonIso K).hom

/-- The canonical map from the original complex to the chosen colimit of its
brutal truncation diagram. -/
@[stacks 0D8Z]
noncomputable abbrev comparisonInv (K : CochainComplex A ℤ)
    [HasColimit (Trunc.diagram K)] : K ⟶ colimit (Trunc.diagram K) :=
  (comparisonIso K).inv

/-- The canonical comparison is the universal map from the chosen colimit to
the canonical brutal-truncation cocone. -/
@[stacks 0D8Z]
theorem comparison_eq_desc (K : CochainComplex A ℤ)
    [HasColimit (Trunc.diagram K)] :
    comparison K = Limits.colimit.desc (Trunc.diagram K) (Trunc.cocone K) := sorry

/-- The inverse comparison is the map induced by the canonical brutal
colimit universal property. -/
@[stacks 0D8Z]
theorem comparisonInv_eq_desc (K : CochainComplex A ℤ)
    [HasColimit (Trunc.diagram K)] :
    comparisonInv K =
      (Trunc.isColimit K).desc (Limits.colimit.cocone (Trunc.diagram K)) := sorry

/-- The comparison is invertible because it is the forward map of the
canonical comparison isomorphism. -/
@[stacks 0D8Z]
noncomputable instance comparisonIsIso (K : CochainComplex A ℤ)
    [HasColimit (Trunc.diagram K)] : IsIso (comparison K) :=
  inferInstance

/-- A chosen-colimit inclusion followed by the canonical comparison is the
corresponding brutal-stage inclusion. -/
@[reassoc (attr := simp), stacks 0D8Z]
theorem ι_comp_comparison (K : CochainComplex A ℤ)
    [HasColimit (Trunc.diagram K)] (n : ℕ) :
    Limits.colimit.ι (Trunc.diagram K) n ≫ comparison K = Trunc.ι K n := sorry

/-- A brutal-stage inclusion followed by the inverse comparison is the
chosen-colimit inclusion. -/
@[reassoc (attr := simp), stacks 0D8Z]
theorem ι_comp_comparisonInv (K : CochainComplex A ℤ)
    [HasColimit (Trunc.diagram K)] (n : ℕ) :
    Trunc.ι K n ≫ comparisonInv K =
      Limits.colimit.ι (Trunc.diagram K) n := sorry

section Functorial

variable [HasColimitsOfShape ℕ (CochainComplex A ℤ)]

/-- Taking the chosen colimit of the functorial brutal truncation diagram. -/
@[stacks 0D8Z]
noncomputable def functor : CochainComplex A ℤ ⥤ CochainComplex A ℤ :=
  Trunc.functor ⋙ (colim : (ℕ ⥤ CochainComplex A ℤ) ⥤ CochainComplex A ℤ)

/-- The brutal-colimit functor evaluates to the chosen colimit of the
corresponding diagram. -/
@[simp, stacks 0D8Z]
theorem functor_obj (K : CochainComplex A ℤ) :
    (functor (A := A)).obj K = colimit (Trunc.diagram K) := sorry

/-- The brutal-colimit functor maps a cochain map by the induced colimit map. -/
@[simp, stacks 0D8Z]
theorem functor_map {K L : CochainComplex A ℤ} (f : K ⟶ L) :
    (functor (A := A)).map f = colimMap (Trunc.map f) := sorry

namespace Comparison

/-- Naturality of the chosen-colimit comparison. -/
@[stacks 0D8Z]
theorem naturality {K L : CochainComplex A ℤ} (f : K ⟶ L) :
    (functor (A := A)).map f ≫ comparison L =
      comparison K ≫ (𝟭 (CochainComplex A ℤ)).map f := sorry

/-- Naturality after simplifying the identity-functor map. -/
@[reassoc, stacks 0D8Z]
theorem naturality_hom {K L : CochainComplex A ℤ} (f : K ⟶ L) :
    (functor (A := A)).map f ≫ comparison L = comparison K ≫ f := sorry

/-- The chosen-colimit comparisons form a natural transformation to the
identity functor. -/
@[stacks 0D8Z]
noncomputable def natTrans : functor (A := A) ⟶ 𝟭 (CochainComplex A ℤ) where
  app K := comparison K
  naturality := fun {K L} f ↦ naturality (A := A) (K := K) (L := L) f

/-- A component of `natTrans` is the canonical colimit comparison. -/
@[simp, stacks 0D8Z]
theorem natTrans_app (K : CochainComplex A ℤ) :
    (natTrans (A := A)).app K = comparison K := sorry

/-- The brutal-colimit functor is canonically naturally isomorphic to the
identity functor. -/
@[stacks 0D8Z]
noncomputable def natIso : functor (A := A) ≅ 𝟭 (CochainComplex A ℤ) :=
  NatIso.ofComponents (fun K ↦ comparisonIso K)
    (fun {K L} f ↦ naturality (A := A) (K := K) (L := L) f)

/-- The forward component of `natIso` is the canonical comparison. -/
@[simp, stacks 0D8Z]
theorem natIso_hom_app (K : CochainComplex A ℤ) :
    (natIso (A := A)).hom.app K = comparison K := sorry

/-- The inverse component of `natIso` is the canonical inverse comparison. -/
@[simp, stacks 0D8Z]
theorem natIso_inv_app (K : CochainComplex A ℤ) :
    (natIso (A := A)).inv.app K = comparisonInv K := sorry

end Comparison

end Functorial

end CategoryTheory.CochainComplex.Brutal.Trunc.Colimit
