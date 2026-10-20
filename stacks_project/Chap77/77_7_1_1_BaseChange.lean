module

public import stacks_project.Chap65.Lemma_65_6_2_OfOver
public import stacks_project.Chap65.Lemma_65_7_3_Pullback
public import stacks_project.Chap66.Definition_66_4_1_Points
public import stacks_project.Chap66.Lemma_66_29_2

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.BaseChange.Map

/-!
# Base change of a module morphism on an algebraic space

Pulling a morphism of quasi-coherent modules on an algebraic space `X` back along the
projection `X ×_B T ⟶ X` associated to a test scheme `T` over `B`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

variable {S : Scheme.{u}} {X B : AlgebraicSpace S} (f : X ⟶ B)
variable {ℱ 𝒢 : X.Modules} [ℱ.IsQuasicoherent] [𝒢.IsQuasicoherent]
variable {T : Over S} (a : ofOver T ⟶ B) (u : ℱ ⟶ 𝒢)

#check (AlgebraicGeometry.AlgebraicSpace.Modules.baseChangeSpace f a : AlgebraicSpace S)

#check (AlgebraicGeometry.AlgebraicSpace.Modules.baseChangeProj f a :
  baseChangeSpace f a ⟶ X)

#check (AlgebraicGeometry.AlgebraicSpace.Modules.baseChangeModule f a ℱ :
  (baseChangeSpace f a).Modules)

#check (AlgebraicGeometry.AlgebraicSpace.Modules.baseChangeModule_eq f a ℱ :
  baseChangeModule f a ℱ = (pullback (Limits.pullback.fst f a)).obj ℱ)

#check (AlgebraicGeometry.AlgebraicSpace.Modules.baseChangeMap f a u :
  baseChangeModule f a ℱ ⟶ baseChangeModule f a 𝒢)

#check (AlgebraicGeometry.AlgebraicSpace.Modules.baseChangeMap_eq f a u :
  baseChangeMap f a u = (pullback (Limits.pullback.fst f a)).map u)

#check (AlgebraicGeometry.AlgebraicSpace.Modules.baseChangeMap_isIso_of_over f a :
  ∀ {T' : Over S} (φ : T' ⟶ T) (u : ℱ ⟶ 𝒢),
    IsIso (baseChangeMap f a u) → IsIso (baseChangeMap f (ofOverMap φ ≫ a) u))

end AlgebraicGeometry.AlgebraicSpace.Modules
