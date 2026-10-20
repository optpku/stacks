module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Perfect.TorDimension
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

attribute [local instance] SheafOfModules.RingedSite.moduleCategoryHasMapBifunctor

/- Lemma 37.61.11: for a pseudo-coherent morphism of schemes, perfectness, local finite
Tor dimension of the structure sheaf over the inverse-image structure sheaf, and finite Tor
dimension of every stalk map are equivalent. -/
@[stacks 069C] #check
  (AlgebraicGeometry.PseudoCoherent.perfect_tfae :
    ∀ {X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S)
      [AlgebraicGeometry.PseudoCoherent f]
      [∀ U : TopologicalSpace.Opens (AlgebraicGeometry.RingedSpace.Hom.inverseImageBase f.toShHom).carrier,
        DerivedCategory.DerivedTensor.Right.Has
          (C := AlgebraicGeometry.RingedSpace.Modules
            ((AlgebraicGeometry.RingedSpace.Hom.inverseImageBase f.toShHom).restrict U.isOpenEmbedding))],
      List.TFAE [AlgebraicGeometry.LocallyOfType RingHom.IsPerfectRingMap f,
        AlgebraicGeometry.RingedSpace.ModuleDerived.LocallyHasFiniteTorDimension
          (X := AlgebraicGeometry.RingedSpace.Hom.inverseImageBase f.toShHom)
          ((AlgebraicGeometry.RingedSpace.ModuleDerived.relativeRestriction f.toShHom).obj
            (AlgebraicGeometry.Scheme.DerivedQCoh.structureSheaf X).obj),
        ∀ x : X, (f.stalkMap x).hom.HasFiniteTorDimension])
