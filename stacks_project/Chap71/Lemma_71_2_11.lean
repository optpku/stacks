module

public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap66.Lemma_66_29_4_Stalk
public import stacks_project.Chap71.Lemma_71_2_3_WeaklyAssociated

/-!
# Lemma 71.2.11

A morphism of quasi-coherent modules on an algebraic space is injective if at
every point of `|X|` either the induced étale stalk map is injective or the
point is not weakly associated to the source.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

variable {S : Scheme.{u}} {X : AlgebraicSpace S}
variable {F G : X.Modules} [F.IsQuasicoherent] [G.IsQuasicoherent]

/-- Lemma 71.2.11: let `S` be a scheme, let `X` be an algebraic space over `S`,
and let `φ : F ⟶ G` be a morphism of quasi-coherent `𝒪_X`-modules. If for every
point `x` of `|X|` either the étale stalk map `F_{x̄} ⟶ G_{x̄}` is injective for
every geometric point `x̄` lying over `x`, or `x ∉ F.weakAss`, then `φ` is a
monomorphism. -/
@[stacks 0CUR]
theorem mono_of_stalkwise_injective_or_not_mem_weakAss
    (φ : F ⟶ G)
    (hφ : ∀ x : Points X,
      (∀ xbar : GeometricPoint X,
          xbar.liesOver x → Function.Injective (stalkModuleCatMap xbar φ)) ∨
        x ∉ F.weakAss) :
    Mono φ :=
  sorry

/-- A morphism of quasi-coherent modules on an algebraic space is a monomorphism
if its étale stalk map is injective at every geometric point over every weakly
associated point of its source. -/
theorem mono_of_injective_on_weakAss
    (φ : F ⟶ G)
    (hφ : ∀ x : Points X, x ∈ F.weakAss →
      ∀ xbar : GeometricPoint X,
        xbar.liesOver x → Function.Injective (stalkModuleCatMap xbar φ)) :
    Mono φ :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules
