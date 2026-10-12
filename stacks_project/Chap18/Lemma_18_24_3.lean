/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent.Chaotic
import StacksCheckRecall

/-!
# Lemma 18.24.3

Quasicoherence on a chaotic site is the tensor compatibility of sections. The comparison map is
owned for arbitrary commutative-ring presheaves, while the sheaf bridge and the equivalence are
owned by their corresponding ReasLib layers.
-/

@[expose] public section

open CategoryTheory
open SheafOfModules.RingedSite

noncomputable section

universe u v w

namespace SheafOfModules

variable {C : Type u} [Category.{v} C]
variable (O : Sheaf (⊥ : GrothendieckTopology C) CommRingCat.{w})
variable [((⊥ : GrothendieckTopology C)).HasSheafCompose
  (forget₂ CommRingCat.{w} RingCat.{w})]
variable [∀ U : C, HasWeakSheafify
  ((⊥ : GrothendieckTopology C).over U) AddCommGrpCat.{w}]
variable [∀ U : C, ((⊥ : GrothendieckTopology C).over U).WEqualsLocallyBijective
  AddCommGrpCat.{w}]
variable (F : ringedSiteModuleCategory.{u, v, w, w}
  (⊥ : GrothendieckTopology C) O)

/- Lemma 18.24.3 (0GZN): F is quasicoherent exactly when
F(V) ⊗[O(V)] O(U) ⟶ F(U) is an isomorphism for every U ⟶ V. -/
@[stacks 0GZN]
#check
  (IsQuasicoherent.iff_isIso_map O F :
    F.IsQuasicoherent ↔
      ∀ ⦃U V : C⦄ (f : U ⟶ V), IsIso (BaseChange.map O F f))

end SheafOfModules
