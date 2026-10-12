/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Noetherian
public import stacks_project.Chap61.Definition_61_28_1
import Mathlib.Tactic.CrossRefAttribute

/-!
# Lemma 61.28.2

On a Noetherian scheme, a constructible `Λ`-sheaf on the pro-étale site
admits a finite locally closed partition on which it is lisse.
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

/-- Lemma 61.28.2: if `X` is a Noetherian scheme, `Λ` is a Noetherian ring, and `I ⊆ Λ`
is an ideal, then every constructible `Λ`-sheaf on `X_proétale` admits a finite
partition of `X` into locally closed subschemes on which its restriction is lisse. -/
@[stacks 09BU]
theorem exists_locallyClosedPartition_isLisse [IsNoetherian X]
    [IsConstructibleLambdaSheaf I F] :
    ∃ (Q : LocallyClosedPartition X), Q.toSet.Finite ∧
      ∀ (s : Q.toSet),
        let T : LocallyCloseds X :=
          ⟨(s : Set X), Q.locallyClosed_of_mem s.property⟩
        IsLisse I (moduleRestrict (LocallyClosedReduction.ι T) F) :=
  sorry

end AlgebraicGeometry.Scheme.ProEt
