/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.BoundedAboveReplacement.Resolution.ForgetBound
public import ReasLib.Algebra.Homology.CochainComplex.BoundedAboveReplacement.Resolution.Map
public import ReasLib.Algebra.Homology.CochainComplex.BoundedAboveReplacement.Resolution.Variable.Map
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Forgetting the Cutoff of Maps of Bounded-Above Resolutions

Cutoff-forgetting acts on maps over arbitrary cochain maps, not only on morphisms inside one
resolution fiber. This file records that operation and its computation and transport API.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace CochainComplex.StrictlyLE.TermsIn.QuasiIsoFrom.Map

variable {A : Type u} [Category.{v} A] [HasZeroMorphisms A] [CategoryWithHomology A]
  {P : ObjectProperty A} {a : ℤ}
  {K L M : CochainComplex A ℤ} {f : K ⟶ L} {g : L ⟶ M}
  {R : QuasiIsoFrom P a K} {S : QuasiIsoFrom P a L} {T : QuasiIsoFrom P a M}

/-- The model morphism obtained by forgetting a cutoff satisfies the variable-bound comparison
square. -/
theorem forgetBound_naturality (m : Map f R S) :
    (Minus.TermsIn.ι P).map ((StrictlyLE.TermsIn.forgetBound P a).map m.modelHom) ≫
        S.forgetBound.comparison =
      R.forgetBound.comparison ≫ f := sorry

/-- Forget the cutoff of a map of fixed-upper-bound resolutions. -/
@[stacks 05T7 "forgetting the cutoff of a map of bounded-above resolutions"]
def forgetBound (m : Map f R S) :
    Minus.TermsIn.QuasiIsoFrom.Map f R.forgetBound S.forgetBound :=
  Minus.TermsIn.QuasiIsoFrom.Map.mk
    ((StrictlyLE.TermsIn.forgetBound P a).map m.modelHom) m.forgetBound_naturality

/-- Cutoff-forgetting maps the bundled fixed-bound model morphism. -/
@[simp]
theorem forgetBound_modelHom (m : Map f R S) :
    m.forgetBound.modelHom = (StrictlyLE.TermsIn.forgetBound P a).map m.modelHom := sorry

/-- Cutoff-forgetting retains the underlying cochain map between resolving complexes. -/
@[simp]
theorem forgetBound_hom (m : Map f R S) : m.forgetBound.hom = m.hom := sorry

/-- Cutoff-forgetting preserves identity resolution maps. -/
@[simp]
theorem forgetBound_id (R : QuasiIsoFrom P a K) :
    (id R).forgetBound = Minus.TermsIn.QuasiIsoFrom.Map.id R.forgetBound := sorry

/-- Cutoff-forgetting preserves composition of resolution maps. -/
@[simp]
theorem forgetBound_comp (m : Map f R S) (n : Map g S T) :
    (comp m n).forgetBound =
      Minus.TermsIn.QuasiIsoFrom.Map.comp m.forgetBound n.forgetBound := sorry

/-- Cutoff-forgetting commutes with reindexing along an equality of base cochain maps. -/
@[simp]
theorem forgetBound_reindex {f' : K ⟶ L} (e : f = f') (m : Map f R S) :
    (reindex e m).forgetBound = Minus.TermsIn.QuasiIsoFrom.Map.reindex e m.forgetBound := sorry

/-- On a map induced by a fiber morphism, cutoff-forgetting agrees with the existing fiber
functor. -/
@[simp]
theorem forgetBound_ofHom {R S : QuasiIsoFrom P a K} (m : R ⟶ S) :
    (ofHom m).forgetBound =
      Minus.TermsIn.QuasiIsoFrom.Map.ofHom (QuasiIsoFrom.forgetBoundHom m) := sorry

end CochainComplex.StrictlyLE.TermsIn.QuasiIsoFrom.Map


