/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Noetherian
public import ReasLib.AlgebraicGeometry.Scheme.ProEtale.AdicSheaf

/-!
# Lisse stratifications of constructible pro-étale sheaves
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Topology TopologicalSpace

noncomputable section

universe u w

namespace AlgebraicGeometry.Scheme.ProEt

variable {X : Scheme.{u}} {Λ : Type w} [CommRing Λ] [IsNoetherianRing Λ]
variable [HasWeakSheafify (topology X) (ModuleCat.{w} Λ)]
variable [∀ U : X.ProEt, HasWeakSheafify ((topology X).over U) (ModuleCat.{w} Λ)]
variable [∀ {Y Z : Scheme.{u}} (f : Y ⟶ Z) (P : Z.ProEtᵒᵖ ⥤ ModuleCat.{w} Λ),
  (baseChange f).op.HasLeftKanExtension P]
variable [∀ {Y : Scheme.{u}}, HasWeakSheafify (topology Y) (ModuleCat.{w} Λ)]
variable [∀ {Y : Scheme.{u}} (U : Y.ProEt),
  HasWeakSheafify ((topology Y).over U) (ModuleCat.{w} Λ)]

variable (I : Ideal Λ) (F : Sheaf (topology X) (ModuleCat.{w} Λ))

/-- A constructible sheaf of modules over a Noetherian ring on the pro-étale site of a
Noetherian scheme admits a finite partition into locally closed subschemes on which its
restriction is lisse. -/
theorem exists_locallyClosedPartition_isLisse [IsNoetherian X]
    [IsConstructibleLambdaSheaf I F] :
    ∃ (Q : LocallyClosedPartition X), Q.toSet.Finite ∧
      ∀ (s : Q.toSet),
        let T : LocallyCloseds X :=
          ⟨(s : Set X), Q.locallyClosed_of_mem s.property⟩
        IsLisse I (moduleRestrict (LocallyClosedReduction.ι T) F) :=
  sorry

end AlgebraicGeometry.Scheme.ProEt
