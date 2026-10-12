/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Topology.Connected.Basic
public import stacks_project.Chap61.Definition_61_28_1
import Mathlib.Tactic.CrossRefAttribute

/-!
# Lemma 61.28.4

On a connected scheme, every lisse constructible `Λ`-sheaf on the pro-étale site is
adic lisse.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Topology TopologicalSpace

noncomputable section

universe u w

namespace AlgebraicGeometry.Scheme.ProEt

variable {X : Scheme.{u}} {Λ : Type w} [CommRing Λ] [IsNoetherianRing Λ]
variable [HasWeakSheafify (topology X) (ModuleCat.{w} Λ)]
variable [∀ U : X.ProEt, HasWeakSheafify ((topology X).over U) (ModuleCat.{w} Λ)]
variable [∀ {Y : Scheme.{u}} (f : Y ⟶ X) (P : X.ProEtᵒᵖ ⥤ ModuleCat.{w} Λ),
  (baseChange f).op.HasLeftKanExtension P]
variable [∀ {Y : Scheme.{u}}, HasWeakSheafify (topology Y) (ModuleCat.{w} Λ)]
variable [∀ {Y : Scheme.{u}} (U : Y.ProEt),
  HasWeakSheafify ((topology Y).over U) (ModuleCat.{w} Λ)]

variable (I : Ideal Λ) (F : Sheaf (topology X) (ModuleCat.{w} Λ))

/-- Lemma 61.28.4: if `X` is a connected scheme, `Λ` is Noetherian, and `I ⊆ Λ` is an
ideal, then every lisse constructible `Λ`-sheaf on `X_proétale` is adic lisse. -/
@[stacks 09BW]
instance instIsAdicLisse_of_isLisse [ConnectedSpace X] [IsLisse I F] :
    IsAdicLisse I F :=
  sorry

end AlgebraicGeometry.Scheme.ProEt
