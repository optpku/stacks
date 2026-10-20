/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.BoundedBelowReplacement.Resolution.ForgetBound
public import ReasLib.Algebra.Homology.CochainComplex.BoundedBelowReplacement.Resolution.Map
public import ReasLib.Algebra.Homology.CochainComplex.BoundedBelowReplacement.Resolution.Variable.Map
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Forgetting the Cutoff of Maps of Bounded-Below Resolutions

Cutoff-forgetting acts on maps over arbitrary cochain maps, not only on morphisms inside one
resolution fiber. This file records that operation and its computation and transport API.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace CochainComplex.StrictlyGE.TermsIn.QuasiIsoTo.Map

variable {A : Type u} [Category.{v} A] [HasZeroMorphisms A] [CategoryWithHomology A]
  {P : ObjectProperty A} {a : ℤ}
  {K L M : CochainComplex A ℤ} {f : K ⟶ L} {g : L ⟶ M}
  {R : QuasiIsoTo P a K} {S : QuasiIsoTo P a L} {T : QuasiIsoTo P a M}

/-- The model morphism obtained by forgetting a cutoff satisfies the variable-bound comparison
square. -/
theorem forgetBound_naturality (m : Map f R S) :
    R.forgetBound.comparison ≫
        (Plus.TermsIn.ι P).map ((StrictlyGE.TermsIn.forgetBound P a).map m.modelHom) =
      f ≫ S.forgetBound.comparison := sorry

/-- Forget the cutoff of a map of fixed-lower-bound resolutions. -/
@[stacks 05T6 "forgetting the cutoff of a map of bounded-below resolutions"]
def forgetBound (m : Map f R S) :
    Plus.TermsIn.QuasiIsoTo.Map f R.forgetBound S.forgetBound :=
  Plus.TermsIn.QuasiIsoTo.Map.mk
    ((StrictlyGE.TermsIn.forgetBound P a).map m.modelHom) m.forgetBound_naturality

/-- Cutoff-forgetting maps the bundled fixed-bound model morphism. -/
@[simp]
theorem forgetBound_modelHom (m : Map f R S) :
    m.forgetBound.modelHom = (StrictlyGE.TermsIn.forgetBound P a).map m.modelHom := sorry

/-- Cutoff-forgetting retains the underlying cochain map between resolving complexes. -/
@[simp]
theorem forgetBound_hom (m : Map f R S) : m.forgetBound.hom = m.hom := sorry

/-- Cutoff-forgetting preserves identity resolution maps. -/
@[simp]
theorem forgetBound_id (R : QuasiIsoTo P a K) :
    (id R).forgetBound = Plus.TermsIn.QuasiIsoTo.Map.id R.forgetBound := sorry

/-- Cutoff-forgetting preserves composition of resolution maps. -/
@[simp]
theorem forgetBound_comp (m : Map f R S) (n : Map g S T) :
    (comp m n).forgetBound =
      Plus.TermsIn.QuasiIsoTo.Map.comp m.forgetBound n.forgetBound := sorry

/-- Cutoff-forgetting commutes with reindexing along an equality of base cochain maps. -/
@[simp]
theorem forgetBound_reindex {f' : K ⟶ L} (e : f = f') (m : Map f R S) :
    (reindex e m).forgetBound = Plus.TermsIn.QuasiIsoTo.Map.reindex e m.forgetBound := sorry

/-- On a map induced by a fiber morphism, cutoff-forgetting agrees with the existing fiber
functor. -/
@[simp]
theorem forgetBound_ofHom {R S : QuasiIsoTo P a K} (m : R ⟶ S) :
    (ofHom m).forgetBound =
      Plus.TermsIn.QuasiIsoTo.Map.ofHom (QuasiIsoTo.forgetBoundHom m) := sorry

end CochainComplex.StrictlyGE.TermsIn.QuasiIsoTo.Map


