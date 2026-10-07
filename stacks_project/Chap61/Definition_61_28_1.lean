module

public import ReasLib.AlgebraicGeometry.Scheme.ProEtale.AdicSheaf
import StacksCheckRecall

/-!
# Constructible and adic sheaves of Λ-modules on the pro-étale site
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

/- Definition 61.28.1 (1): A sheaf is complete for its ideal-power quotient tower and each reduction is constructible. -/
@[stacks 09BT] #check (AlgebraicGeometry.Scheme.ProEt.IsConstructibleLambdaSheaf :
    Ideal Λ → Sheaf (topology X) (ModuleCat.{w} Λ) → Prop)

/- Definition 61.28.1 (2): A constructible Λ-sheaf is lisse when each ideal-power reduction is locally constant. -/
@[stacks 09BT] #check (AlgebraicGeometry.Scheme.ProEt.IsLisse :
    Ideal Λ → Sheaf (topology X) (ModuleCat.{w} Λ) → Prop)

/- Definition 61.28.1 (3): A sheaf is locally isomorphic to the completed constant sheaf of an I-adically complete module with finite reduction modulo I. -/
@[stacks 09BT] #check (AlgebraicGeometry.Scheme.ProEt.IsAdicLisse :
    Ideal Λ → Sheaf (topology X) (ModuleCat.{w} Λ) → Prop)

/- Definition 61.28.1 (4): Every affine open has constructible locally closed strata on which the inverse image is adic lisse. -/
@[stacks 09BT] #check (AlgebraicGeometry.Scheme.ProEt.IsAdicConstructible :
    Ideal Λ → Sheaf (topology X) (ModuleCat.{w} Λ) → Prop)

end AlgebraicGeometry.Scheme.ProEt
