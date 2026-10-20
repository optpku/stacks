/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Topology.Sheaf.ClosedEmbedding
public import ReasLib.Topology.Sheaf.Cohomology.Pushforward
import Mathlib.Tactic.CrossRefAttribute

/-!
# Sheaf cohomology under a closed embedding

The canonical direct-image comparison is invertible in every degree for a closed embedding.
This leaf owns both its objectwise form over an open and its source-facing global specialization.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Abelian Opposite TopologicalSpace TopCat

noncomputable section

universe u

namespace CategoryTheory.Sheaf.ClosedEmbedding

variable {X Y : TopCat.{u}}

/-- Direct image along a closed embedding identifies cohomology over an open with cohomology
over its inverse image. The inverse applies exact direct image to an extension and precomposes
with the adjoint of the inverse free abelian Yoneda comparison. -/
noncomputable def comparisonIso (f : X ⟶ Y) (hf : Topology.IsClosedEmbedding f)
    (F : X.Sheaf AddCommGrpCat.{u}) (p : ℕ) (U : Opens Y) :
    ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).obj F).H' p U ≅
      F.H' p ((Opens.map f).obj U) :=
  have hexact := (exactFunctor_iff _).1
    (TopCat.Sheaf.ClosedEmbedding.AddCommGrp.pushforwardExact hf)
  -- Local instance justification (proof-local temporary data): mapping Ext requires the
  -- finite-limit preservation supplied by exact direct image for this closed embedding.
  haveI := hexact.1
  -- Local instance justification (proof-local temporary data): mapping Ext also requires
  -- the finite-colimit preservation supplied by the same exactness proof.
  haveI := hexact.2
  { hom := CategoryTheory.Sheaf.pushforwardCohomologyMap f F p U
    inv := AddCommGrpCat.ofHom <|
      ((Ext.mk₀
          ((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} f).homEquiv _ _
            (TopCat.Sheaf.FreeAbelianYoneda.pullbackIso f U).inv)).precomp
          ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).obj F) (zero_add p)).comp
        ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).mapExtAddHom
          (GrothendieckTopology.FreeAbelianYoneda.obj
            (Opens.grothendieckTopology X) ((Opens.map f).obj U)) F p)
    hom_inv_id := sorry
    inv_hom_id := sorry }

/-- The forward map of the closed-embedding identification is the canonical direct-image
cohomology comparison. -/
@[simp]
theorem comparisonIso_hom (f : X ⟶ Y) (hf : Topology.IsClosedEmbedding f)
    (F : X.Sheaf AddCommGrpCat.{u}) (p : ℕ) (U : Opens Y) :
    (comparisonIso f hf F p U).hom =
      CategoryTheory.Sheaf.pushforwardCohomologyMap f F p U := rfl

/-- The canonical direct-image cohomology comparison along a closed embedding is an isomorphism
over every open and in every degree. -/
@[stacks 02UV "closed-embedding cohomology comparison"]
theorem comparison_isIso (f : X ⟶ Y) (hf : Topology.IsClosedEmbedding f)
    (F : X.Sheaf AddCommGrpCat.{u}) (p : ℕ) (U : Opens Y) :
    IsIso (CategoryTheory.Sheaf.pushforwardCohomologyMap f F p U) :=
  (comparisonIso f hf F p U).isIso_hom

/-- The canonical comparison from global cohomology of the direct image to global cohomology on
the source of a closed embedding is an isomorphism in every degree. -/
@[stacks 02UV]
theorem globalComparison_isIso (f : X ⟶ Y) (hf : Topology.IsClosedEmbedding f)
    (F : X.Sheaf AddCommGrpCat.{u}) (p : ℕ) :
    IsIso (CategoryTheory.Sheaf.pushforwardCohomologyMap f F p (⊤ : Opens Y)) :=
  comparison_isIso f hf F p ⊤

end CategoryTheory.Sheaf.ClosedEmbedding
