module

public import ReasLib.AlgebraicGeometry.Scheme.Module.CohenMacaulay
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry
open scoped ENat

universe u

variable {X : Scheme.{u}} [IsLocallyNoetherian X]
variable (ℱ : X.Modules) [ℱ.IsCoherent]

/- Definition 30.11.4: A coherent module on a locally Noetherian scheme is
Cohen-Macaulay if and only if it satisfies `(S_k)` for every `k : ℕ`.
-/
@[stacks 0343] #check (AlgebraicGeometry.Scheme.Modules.cohenMacaulay_iff_forall_satisfiesSerreConditionS ℱ :
    AlgebraicGeometry.Scheme.Modules.CohenMacaulay ℱ ↔
      ∀ k : ℕ, AlgebraicGeometry.Scheme.Modules.satisfiesSerreConditionS ℱ k)

variable {Y : LocallyRingedSpace.{u}}
variable [∀ y : Y, IsNoetherianRing (Y.presheaf.stalk y)]
variable (𝒢 : Y.Modules)
variable [AlgebraicGeometry.LocallyRingedSpace.Modules.CohenMacaulay 𝒢]
variable (y : Y)

section NonzeroStalk
variable [Nontrivial (RingedSpace.stalkModuleCat 𝒢 y)]

#check (AlgebraicGeometry.LocallyRingedSpace.Modules.CohenMacaulay 𝒢 : Prop)

#check (AlgebraicGeometry.LocallyRingedSpace.Modules.CohenMacaulay.stalk_cohenMacaulay 𝒢 y :
  Module.CohenMacaulay (Y.presheaf.stalk y) (RingedSpace.stalkModuleCat 𝒢 y))

#check (AlgebraicGeometry.LocallyRingedSpace.Modules.CohenMacaulay.instStalkCohenMacaulay 𝒢 y :
  Module.CohenMacaulay (Y.presheaf.stalk y) (RingedSpace.stalkModuleCat 𝒢 y))

end NonzeroStalk

#check (AlgebraicGeometry.LocallyRingedSpace.Modules.CohenMacaulay.hasFiniteStalks 𝒢 :
  AlgebraicGeometry.LocallyRingedSpace.Modules.HasFiniteStalks 𝒢)

#check (AlgebraicGeometry.LocallyRingedSpace.Modules.CohenMacaulay.instHasFiniteStalks 𝒢 :
  AlgebraicGeometry.LocallyRingedSpace.Modules.HasFiniteStalks 𝒢)

#check (AlgebraicGeometry.LocallyRingedSpace.Modules.cohenMacaulay_iff_forall_serreConditionS 𝒢 :
  AlgebraicGeometry.LocallyRingedSpace.Modules.CohenMacaulay 𝒢 ↔
    ∀ y : Y, ∀ k : ℕ,
      Module.SerreConditionS (Y.presheaf.stalk y) (RingedSpace.stalkModuleCat 𝒢 y) k)

#check (AlgebraicGeometry.LocallyRingedSpace.Modules.cohenMacaulay_iff_forall_satisfiesSerreConditionS 𝒢 :
  AlgebraicGeometry.LocallyRingedSpace.Modules.CohenMacaulay 𝒢 ↔
    ∀ k : ℕ,
      AlgebraicGeometry.LocallyRingedSpace.Modules.satisfiesSerreConditionS 𝒢 k)

#check (AlgebraicGeometry.Scheme.Modules.hasFiniteStalks_of_isFinitePresentation ℱ :
  AlgebraicGeometry.LocallyRingedSpace.Modules.HasFiniteStalks
    (X := X.toLocallyRingedSpace) ℱ)

#check (AlgebraicGeometry.Scheme.Modules.instHasFiniteStalksOfIsFinitePresentation ℱ :
  AlgebraicGeometry.LocallyRingedSpace.Modules.HasFiniteStalks
    (X := X.toLocallyRingedSpace) ℱ)

#check (AlgebraicGeometry.Scheme.Modules.instHasFiniteStalksOfIsCoherent ℱ :
  AlgebraicGeometry.LocallyRingedSpace.Modules.HasFiniteStalks
    (X := X.toLocallyRingedSpace) ℱ)

variable (x : X) (k : ℕ)

#check (AlgebraicGeometry.Scheme.Modules.satisfiesSerreConditionS ℱ k : Prop)

#check (AlgebraicGeometry.Scheme.Modules.satisfiesSerreConditionS_def ℱ k :
  AlgebraicGeometry.Scheme.Modules.satisfiesSerreConditionS ℱ k =
    (∀ x : X,
      WithBot.some (moduleDepth (X.presheaf.stalk x) (RingedSpace.stalkModuleCat ℱ x) : ℕ∞) ≥
        min (k : WithBot ℕ∞)
          (Module.supportDim (X.presheaf.stalk x) (RingedSpace.stalkModuleCat ℱ x))))

#check (AlgebraicGeometry.Scheme.Modules.satisfiesSerreConditionS_iff ℱ k :
  AlgebraicGeometry.Scheme.Modules.satisfiesSerreConditionS ℱ k ↔
    ∀ x : X,
      WithBot.some (moduleDepth (X.presheaf.stalk x) (RingedSpace.stalkModuleCat ℱ x) : ℕ∞) ≥
        min (k : WithBot ℕ∞)
          (Module.supportDim (X.presheaf.stalk x) (RingedSpace.stalkModuleCat ℱ x)))

variable [AlgebraicGeometry.Scheme.Modules.CohenMacaulay ℱ]

section NonzeroSchemeStalk
variable [Nontrivial (RingedSpace.stalkModuleCat ℱ x)]

#check (AlgebraicGeometry.Scheme.Modules.CohenMacaulay ℱ : Prop)

#check (AlgebraicGeometry.Scheme.Modules.CohenMacaulay.stalk (ℱ := ℱ) x :
  Module.CohenMacaulay (X.presheaf.stalk x) (RingedSpace.stalkModuleCat ℱ x))

#check (AlgebraicGeometry.Scheme.Modules.CohenMacaulay.instStalkCohenMacaulay (ℱ := ℱ) x :
  Module.CohenMacaulay (X.presheaf.stalk x) (RingedSpace.stalkModuleCat ℱ x))

end NonzeroSchemeStalk

#check (AlgebraicGeometry.Scheme.Modules.cohenMacaulay_iff_forall_serreConditionS ℱ :
  AlgebraicGeometry.Scheme.Modules.CohenMacaulay ℱ ↔
    ∀ x : X, ∀ k : ℕ,
      Module.SerreConditionS (X.presheaf.stalk x) (RingedSpace.stalkModuleCat ℱ x) k)

#check (AlgebraicGeometry.Scheme.Modules.IsCoherent.iff_exists_affineOpenCover ℱ :
  ℱ.IsCoherent ↔
    ℱ.IsQuasicoherent ∧
      ∃ 𝒰 : X.AffineOpenCover,
        ∀ i : 𝒰.I₀,
          Module.Finite
            Γ(X, 𝒰.openCover.f i |>.opensRange)
            Γ(ℱ, 𝒰.openCover.f i |>.opensRange))
