/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.CategoryTheory.ObjectProperty.FiniteProducts
import Mathlib.Tactic.CrossRefAttribute

/-!
# Finite biproducts of quasicoherent module sheaves

Quasicoherence is invariant under isomorphism and is closed under binary biproducts.  The
object-property instances in this file let downstream arguments use those facts through the
standard `CategoryTheory.ObjectProperty` API.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.ObjectProperty

noncomputable section

universe w u v

namespace SheafOfModules

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C} {R : Sheaf J RingCat.{w}}
variable [∀ X, (J.over X).HasSheafCompose (forget₂ RingCat.{w} AddCommGrpCat.{w})]
variable [∀ X, HasSheafify (J.over X) AddCommGrpCat.{w}]
variable [∀ X, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{w}]

namespace IsQuasicoherent

/-- Quasicoherence transports across an isomorphism of module sheaves. -/
theorem ofIso {M N : SheafOfModules.{w} R} (e : M ≅ N) [M.IsQuasicoherent] :
    N.IsQuasicoherent := sorry

/-- Lemma 17.10.2 (01BF), in site-theoretic form: a binary biproduct of quasicoherent module
sheaves is quasicoherent. -/
@[stacks 01BF "binary biproduct"]
theorem biprod {M N : SheafOfModules.{w} R} [HasBinaryBiproduct M N]
    [M.IsQuasicoherent] [N.IsQuasicoherent] :
    (M ⊞ N).IsQuasicoherent := sorry

/-- The canonical quasicoherence instance on a binary biproduct. -/
instance instBiprod {M N : SheafOfModules.{w} R} [HasBinaryBiproduct M N]
    [M.IsQuasicoherent] [N.IsQuasicoherent] :
    (M ⊞ N).IsQuasicoherent := sorry

end IsQuasicoherent

namespace isQuasicoherent

/-- The quasicoherent object property is invariant under isomorphism. -/
instance isClosedUnderIsomorphisms :
    (SheafOfModules.isQuasicoherent R).IsClosedUnderIsomorphisms := sorry

section

variable [HasBinaryProducts C]
variable [HasSheafify J AddCommGrpCat.{w}]
variable [J.HasSheafCompose (forget₂ RingCat.{w} AddCommGrpCat.{w})]

/-- The quasicoherent object property is closed under binary products. -/
instance isClosedUnderBinaryProducts :
    (SheafOfModules.isQuasicoherent R).IsClosedUnderBinaryProducts := sorry

end

end isQuasicoherent

end SheafOfModules
