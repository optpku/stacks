module

public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap85.Lemma_85_34_3_Derived

/-!
# Lemma 85.34.3

Let `S` be a scheme, `X` an algebraic space over `S`, and `U` a simplicial
algebraic space over `S`, with augmentation `a : U ⟶ X`. If `a` is an fppf
hypercovering of `X`, then for a quasi-coherent `𝒪_X`-module `F` the canonical
map `F ⟶ Ra_*(a^* F)` is an isomorphism. Here `a` is the Section 85.32
spaces-étale augmentation of ringed topoi.
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace.Simplicial
open Functor
open scoped Simplicial

noncomputable section

namespace AlgebraicGeometry.AlgebraicSpace.Simplicial

variable {S : Scheme.{u}} {X : AlgebraicSpace S}
variable {U : SimplicialObject (AlgebraicSpace S)}
variable (a : U ⟶ (const SimplexCategoryᵒᵖ).obj X)

/-- Lemma 85.34.3: Let `S` be a scheme. Let `X` be an algebraic space over `S`.
Let `U` be a simplicial algebraic space over `S`. Let `a : U ⟶ X` be an
augmentation. If `a : U ⟶ X` is an fppf hypercovering of `X`, then for `F` a
quasi-coherent `𝒪_X`-module the map `F ⟶ Ra_*(a^* F)` is an isomorphism. Here
`a : Sh(U_étale) ⟶ Sh(X_étale)` is the Section 85.32 spaces-étale augmentation
`spacesEtaleAugmentationHom`. -/
@[stacks 0DHE]
theorem toPushforwardDerived_isIso (ha : IsFppfHypercovering a)
    (F : RingedSite.ModuleCat.{u} (spacesRingedSite X)) [F.IsQuasicoherent] :
    IsIso (toPushforwardDerived a F) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Simplicial

end
