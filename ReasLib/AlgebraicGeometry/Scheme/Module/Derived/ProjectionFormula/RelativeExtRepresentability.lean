module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.ProjectionFormula.RelativeExt
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Pushforward.Perfect.PseudoCoherentDual

@[expose] public section

/-!
# Representability of relative Ext

Relative Ext against a pseudo-coherent complex and a relatively perfect complex has a
pseudo-coherent representative on the base, unique up to isomorphism.
-/

open AlgebraicGeometry CategoryTheory
open CategoryTheory.MonoidalClosed
open RingedSpace.Module.Derived RingedSpace.ModuleDerived

noncomputable section

universe u

attribute [local instance] SheafOfModules.RingedSite.moduleCategoryHasMapBifunctor

namespace AlgebraicGeometry.Scheme.ModuleDerived.ProjectionFormula

/-- For a flat proper finitely presented morphism with quasi-compact and quasi-separated base,
the relative Ext functor associated to a pseudo-coherent complex and a relatively perfect
complex has a pseudo-coherent representative on the base. -/
theorem existsPseudoCoherentRelativeExtRepresentation {X S : Scheme.{u}} (f : X ⟶ S)
    [CompactSpace S] [QuasiSeparatedSpace S]
    [Flat f] [IsProper f] [Scheme.Hom.FinitePresentation f]
    [∀ U : TopologicalSpace.Opens (RingedSpace.Hom.inverseImageBase f.toShHom).carrier,
      DerivedCategory.DerivedTensor.Right.Has
        (C := RingedSpace.Modules
          ((RingedSpace.Hom.inverseImageBase f.toShHom).restrict U.isOpenEmbedding))]
    [KFlat.HomotopyTensorDescends X.toRingedSpace]
    [KFlat.TensorDescends X.toRingedSpace]
    [KFlat.IsLocalization X.toRingedSpace]
    [MonoidalClosed (RingedSpace.ModuleDerived X.toRingedSpace)]
    [KFlat.HomotopyTensorDescends S.toRingedSpace]
    [KFlat.TensorDescends S.toRingedSpace]
    [KFlat.IsLocalization S.toRingedSpace]
    [MonoidalClosed (RingedSpace.ModuleDerived S.toRingedSpace)]
    (E K : RingedSpace.ModuleDerived X.toRingedSpace)
    (hE : IsPerfectRelativeTo f E)
    (hK : RingedSpace.ModuleDerived.IsPseudoCoherent K) :
    ∃ L : RingedSpace.ModuleDerived S.toRingedSpace,
      RingedSpace.ModuleDerived.IsPseudoCoherent L ∧
        RepresentsRelativeExt f K E L := sorry

/-- Any two pseudo-coherent representatives of the same relative Ext functor are isomorphic
in the derived category of the base. -/
theorem relativeExtRepresentation_unique {X S : Scheme.{u}} (f : X ⟶ S)
    [CompactSpace S] [QuasiSeparatedSpace S]
    [Flat f] [IsProper f] [Scheme.Hom.FinitePresentation f]
    [∀ U : TopologicalSpace.Opens (RingedSpace.Hom.inverseImageBase f.toShHom).carrier,
      DerivedCategory.DerivedTensor.Right.Has
        (C := RingedSpace.Modules
          ((RingedSpace.Hom.inverseImageBase f.toShHom).restrict U.isOpenEmbedding))]
    [KFlat.HomotopyTensorDescends X.toRingedSpace]
    [KFlat.TensorDescends X.toRingedSpace]
    [KFlat.IsLocalization X.toRingedSpace]
    [MonoidalClosed (RingedSpace.ModuleDerived X.toRingedSpace)]
    [KFlat.HomotopyTensorDescends S.toRingedSpace]
    [KFlat.TensorDescends S.toRingedSpace]
    [KFlat.IsLocalization S.toRingedSpace]
    [MonoidalClosed (RingedSpace.ModuleDerived S.toRingedSpace)]
    (E K : RingedSpace.ModuleDerived X.toRingedSpace)
    (hE : IsPerfectRelativeTo f E)
    (hK : RingedSpace.ModuleDerived.IsPseudoCoherent K)
    (L L' : RingedSpace.ModuleDerived S.toRingedSpace)
    (hL : RingedSpace.ModuleDerived.IsPseudoCoherent L)
    (hL' : RingedSpace.ModuleDerived.IsPseudoCoherent L')
    (representsL : RepresentsRelativeExt f K E L)
    (representsL' : RepresentsRelativeExt f K E L') :
    IsIsomorphic L L' := sorry

end AlgebraicGeometry.Scheme.ModuleDerived.ProjectionFormula
