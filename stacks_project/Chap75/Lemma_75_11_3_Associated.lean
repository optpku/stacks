/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Limits.Preserves.Finite
public import stacks_project.Chap66.Definition_66_29_1_QCoh
public import stacks_project.Chap67.Definition_67_20_2_Affine
public import stacks_project.Chap69.Lemma_69_16_2_Tensor

/-!
# Associated quasi-coherent modules on algebraic spaces

An `A`-module `M`, with `A = Γ(X, 𝒪_X)`, determines the quasi-coherent `𝒪_X`-module
`M ⊗_A 𝒪_X` by pulling the affine associated sheaf back along étale maps to `Spec A`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The morphism of `𝒪_X`-modules induced by an `A`-linear map, assembled from the
affine associated-module functor and scheme pullback along `etaleToSpecA`. -/
noncomputable def tensorOXMap {S : Scheme.{u}} (X : AlgebraicSpace S)
    {M N : ModuleCat.{u} (globalSectionsRing X)} (f : M ⟶ N) :
    tensorOX X M ⟶ tensorOX X N where
  val :=
    { app := fun V ↦
        ((Scheme.Modules.pullback (etaleToSpecA X V.unop)).map
          ((tilde.functor (globalSectionsRing X)).map f)).val.app (op ⊤)
      naturality := sorry }

/-- The functor sending an `A`-module to the associated `𝒪_X`-module `M ⊗_A 𝒪_X`. -/
noncomputable def tensorOXFunctor {S : Scheme.{u}} (X : AlgebraicSpace S) :
    ModuleCat.{u} (globalSectionsRing X) ⥤ X.Modules where
  obj M := tensorOX X M
  map f := tensorOXMap X f
  map_id := sorry
  map_comp := sorry

/-- On objects, `tensorOXFunctor` recovers `tensorOX`. -/
theorem tensorOXFunctor_obj {S : Scheme.{u}} (X : AlgebraicSpace S)
    (M : ModuleCat.{u} (globalSectionsRing X)) :
    (tensorOXFunctor X).obj M = tensorOX X M :=
  sorry

namespace QCoh

/-- The functor sending an `A`-module to the associated quasi-coherent `𝒪_X`-module. -/
noncomputable def tensorOX {S : Scheme.{u}} (X : AlgebraicSpace S) :
    ModuleCat.{u} (globalSectionsRing X) ⥤ QCoh X :=
  (quasiCoherentModuleProperty X).lift (tensorOXFunctor X) fun M ↦
    instIsQuasicoherent_tensorOX X M

/-- The underlying `𝒪_X`-module of `QCoh.tensorOX` is `tensorOXFunctor`. -/
theorem tensorOX_obj {S : Scheme.{u}} (X : AlgebraicSpace S)
    (M : ModuleCat.{u} (globalSectionsRing X)) :
    ((tensorOX X).obj M).obj = (tensorOXFunctor X).obj M :=
  sorry

/-- Forgetting quasi-coherence after `QCoh.tensorOX` recovers `tensorOXFunctor`. -/
theorem inclusion_tensorOX {S : Scheme.{u}} (X : AlgebraicSpace S)
    (M : ModuleCat.{u} (globalSectionsRing X)) :
    (inclusion X).obj ((tensorOX X).obj M) = (tensorOXFunctor X).obj M :=
  sorry

/-- On an affine algebraic space, the associated quasi-coherent module functor is additive. -/
instance tensorOX.additive {S : Scheme.{u}} (X : AlgebraicSpace S) [IsAffine X] :
    (tensorOX X).Additive :=
  sorry

/-- On an affine algebraic space, the associated quasi-coherent module functor preserves
finite limits. -/
instance tensorOX.preservesFiniteLimits {S : Scheme.{u}} (X : AlgebraicSpace S)
    [IsAffine X] : PreservesFiniteLimits (tensorOX X) :=
  sorry

/-- On an affine algebraic space, the associated quasi-coherent module functor preserves
finite colimits. -/
instance tensorOX.preservesFiniteColimits {S : Scheme.{u}} (X : AlgebraicSpace S)
    [IsAffine X] : PreservesFiniteColimits (tensorOX X) :=
  sorry

end QCoh

end AlgebraicGeometry.AlgebraicSpace
