module

public import ReasLib.Algebra.Homology.DerivedCategory.Perfect
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Perfect.Relative.Fiber
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.PseudoCoherent.Relative.GlobalSections

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped CartesianClosed CategoryTheory.DerivedCategory.DerivedTensor

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.DerivedQCoh

/-- If a separated, finitely presented, flat scheme morphism has affine base and
`RΓ(X, E ⊗ᴸ K)` is perfect for every perfect `E`, then `K` is perfect over the base. -/
theorem isPerfectOver_of_globalSectionsTensor
    {A : Type u} [CommRing A] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of A)) [IsSeparated f]
    [Scheme.Hom.FinitePresentation f] [Flat f] (K : DerivedQCoh X)
    (hperfect : ∀ E : RingedSpace.ModuleDerived X.toRingedSpace,
      RingedSpace.ModuleDerived.IsPerfect E →
        DerivedCategory.IsPerfect
          ((Scheme.FlatPullbackSections.baseSections f).obj (E ⊗ᴸ K.obj))) :
    RingedSpace.ModuleDerived.IsPerfectOver f.toShHom K.obj := sorry

end AlgebraicGeometry.Scheme.DerivedQCoh
