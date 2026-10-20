/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Limits.Preserves.Finite
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.ToSpec
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Affine

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

/-- The map induced by the identity of a module is the identity of its associated module. -/
theorem tensorOXMap_id {S : Scheme.{u}} (X : AlgebraicSpace S)
    (M : ModuleCat.{u} (globalSectionsRing X)) :
    tensorOXMap X (𝟙 M) = 𝟙 (tensorOX X M) :=
  sorry

/-- The map induced by a composite is the composite of the induced associated-module maps. -/
theorem tensorOXMap_comp {S : Scheme.{u}} (X : AlgebraicSpace S)
    {M N P : ModuleCat.{u} (globalSectionsRing X)} (f : M ⟶ N) (g : N ⟶ P) :
    tensorOXMap X (f ≫ g) = tensorOXMap X f ≫ tensorOXMap X g :=
  sorry

/-- The functor sending an `A`-module to the associated `𝒪_X`-module `M ⊗_A 𝒪_X`. -/
noncomputable def tensorOXFunctor {S : Scheme.{u}} (X : AlgebraicSpace S) :
    ModuleCat.{u} (globalSectionsRing X) ⥤ X.Modules where
  obj M := tensorOX X M
  map f := tensorOXMap X f
  map_id := tensorOXMap_id X
  map_comp := tensorOXMap_comp X

/-- On objects, `tensorOXFunctor` recovers `tensorOX`. -/
theorem tensorOXFunctor_obj {S : Scheme.{u}} (X : AlgebraicSpace S)
    (M : ModuleCat.{u} (globalSectionsRing X)) :
    (tensorOXFunctor X).obj M = tensorOX X M :=
  rfl

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
  rfl

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

