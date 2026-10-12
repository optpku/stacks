/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.Bounded
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Cohomology.Basic
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Perfect
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.RelativeRestriction
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.TorDimension
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.FlatOver
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.FourierMukai
public import ReasLib.AlgebraicGeometry.Scheme.Module.Support.Proper
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Flat
public import ReasLib.AlgebraicGeometry.Scheme.Regular
public import ReasLib.CategoryTheory.DerivedCategory.CohomologyIn.Bounded
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

open AlgebraicGeometry CategoryTheory
open DerivedCategory.TStructure

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.FourierMukai

/-- A bounded coherent kernel with proper cohomological support over the target and finite
relative Tor dimension induces a Fourier--Mukai functor preserving bounded coherent objects. -/
@[stacks 0FYU "finite relative Tor dimension preservation"]
theorem mapsBoundedCoherent_of_finiteTorDimension
    {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    [IsNoetherian S] [Scheme.Hom.FiniteType f] [Scheme.Hom.FiniteType g]
    (K : RingedSpace.ModuleDerived (Limits.pullback f g).toRingedSpace)
    (hK_coherent : DerivedCategory.cohomologyIn
      (SheafOfModules.isCoherent (Limits.pullback f g).toRingedSpace.ringCatSheaf) K)
    (hK_bounded : (t.bounded : ObjectProperty
      (RingedSpace.ModuleDerived (Limits.pullback f g).toRingedSpace)) K)
    [∀ i : ℤ, Scheme.Modules.HasProperSupportOver
      (Limits.pullback.snd f g) (RingedSpace.ModuleDerived.cohomologySheaf K i)]
    (hK_tor : RingedSpace.HasFiniteTorDimension
      ((RingedSpace.ModuleDerived.relativeRestriction
        (Limits.pullback.fst f g).toShHom).obj K)) :
    (DerivedCategory.cohomologyIn
        (SheafOfModules.isCoherent X.toRingedSpace.ringCatSheaf) ⊓
      (t.bounded : ObjectProperty (RingedSpace.ModuleDerived X.toRingedSpace))) ≤
        (DerivedCategory.cohomologyIn
            (SheafOfModules.isCoherent Y.toRingedSpace.ringCatSheaf) ⊓
          (t.bounded : ObjectProperty
            (RingedSpace.ModuleDerived Y.toRingedSpace))).inverseImage
              (FourierMukai.functor f g K) := sorry

/-- A bounded coherent kernel with a bounded coherent representative that is termwise flat over
the source and has termwise proper support over the target induces bounded coherent preservation. -/
@[stacks 0FYU "flat coherent representative preservation"]
theorem mapsBoundedCoherent_of_flatCoherentRepresentative
    {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    [IsNoetherian S] [Scheme.Hom.FiniteType f] [Scheme.Hom.FiniteType g]
    (K : RingedSpace.ModuleDerived (Limits.pullback f g).toRingedSpace)
    (hK_coherent : DerivedCategory.cohomologyIn
      (SheafOfModules.isCoherent (Limits.pullback f g).toRingedSpace.ringCatSheaf) K)
    (hK_bounded : (t.bounded : ObjectProperty
      (RingedSpace.ModuleDerived (Limits.pullback f g).toRingedSpace)) K)
    (𝒦 : CochainComplex (Limits.pullback f g).toRingedSpace.Modules ℤ)
    (eK : DerivedCategory.Q.obj 𝒦 ≅ K)
    (h𝒦_bounded : CochainComplex.bounded
      (Limits.pullback f g).toRingedSpace.Modules 𝒦)
    [∀ i : ℤ, (𝒦.X i).IsCoherent]
    [∀ i : ℤ, SheafOfModules.IsFlatOver
      (𝒦.X i) (Limits.pullback.fst f g).toShHom]
    [∀ i : ℤ, Scheme.Modules.HasProperSupportOver
      (Limits.pullback.snd f g) (𝒦.X i)] :
    (DerivedCategory.cohomologyIn
        (SheafOfModules.isCoherent X.toRingedSpace.ringCatSheaf) ⊓
      (t.bounded : ObjectProperty (RingedSpace.ModuleDerived X.toRingedSpace))) ≤
        (DerivedCategory.cohomologyIn
            (SheafOfModules.isCoherent Y.toRingedSpace.ringCatSheaf) ⊓
          (t.bounded : ObjectProperty
            (RingedSpace.ModuleDerived Y.toRingedSpace))).inverseImage
              (FourierMukai.functor f g K) := sorry

/-- If the source scheme is regular, proper cohomological support of a bounded coherent kernel
suffices for its Fourier--Mukai functor to preserve bounded coherent objects. -/
@[stacks 0FYU "regular source preservation"]
theorem mapsBoundedCoherent_of_regular
    {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    [IsNoetherian S] [Scheme.Hom.FiniteType f] [Scheme.Hom.FiniteType g]
    [Scheme.Regular X]
    (K : RingedSpace.ModuleDerived (Limits.pullback f g).toRingedSpace)
    (hK_coherent : DerivedCategory.cohomologyIn
      (SheafOfModules.isCoherent (Limits.pullback f g).toRingedSpace.ringCatSheaf) K)
    (hK_bounded : (t.bounded : ObjectProperty
      (RingedSpace.ModuleDerived (Limits.pullback f g).toRingedSpace)) K)
    [∀ i : ℤ, Scheme.Modules.HasProperSupportOver
      (Limits.pullback.snd f g) (RingedSpace.ModuleDerived.cohomologySheaf K i)] :
    (DerivedCategory.cohomologyIn
        (SheafOfModules.isCoherent X.toRingedSpace.ringCatSheaf) ⊓
      (t.bounded : ObjectProperty (RingedSpace.ModuleDerived X.toRingedSpace))) ≤
        (DerivedCategory.cohomologyIn
            (SheafOfModules.isCoherent Y.toRingedSpace.ringCatSheaf) ⊓
          (t.bounded : ObjectProperty
            (RingedSpace.ModuleDerived Y.toRingedSpace))).inverseImage
              (FourierMukai.functor f g K) := sorry

/-- A perfect kernel with proper cohomological support over a target flat over the base induces a
Fourier--Mukai functor preserving bounded coherent objects. -/
@[stacks 0FYU "perfect kernel over a flat target"]
theorem mapsBoundedCoherent_of_perfect_of_flat
    {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    [IsNoetherian S] [Scheme.Hom.FiniteType f] [Scheme.Hom.FiniteType g] [Flat g]
    (K : RingedSpace.ModuleDerived (Limits.pullback f g).toRingedSpace)
    (hK_coherent : DerivedCategory.cohomologyIn
      (SheafOfModules.isCoherent (Limits.pullback f g).toRingedSpace.ringCatSheaf) K)
    (hK_bounded : (t.bounded : ObjectProperty
      (RingedSpace.ModuleDerived (Limits.pullback f g).toRingedSpace)) K)
    (hK_perfect : RingedSpace.ModuleDerived.IsPerfect K)
    [∀ i : ℤ, Scheme.Modules.HasProperSupportOver
      (Limits.pullback.snd f g) (RingedSpace.ModuleDerived.cohomologySheaf K i)] :
    (DerivedCategory.cohomologyIn
        (SheafOfModules.isCoherent X.toRingedSpace.ringCatSheaf) ⊓
      (t.bounded : ObjectProperty (RingedSpace.ModuleDerived X.toRingedSpace))) ≤
        (DerivedCategory.cohomologyIn
            (SheafOfModules.isCoherent Y.toRingedSpace.ringCatSheaf) ⊓
          (t.bounded : ObjectProperty
            (RingedSpace.ModuleDerived Y.toRingedSpace))).inverseImage
              (FourierMukai.functor f g K) := sorry

/-- If the source morphism is proper, every cohomology sheaf of a bounded coherent kernel on the
fiber product has proper support over the target. -/
@[stacks 0FYU "proper support of cohomology sheaves"]
theorem cohomologySheaf_hasProperSupportOver_of_isProper
    {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    [IsNoetherian S] [Scheme.Hom.FiniteType f]
    [Scheme.Hom.FiniteType g] [IsProper f]
    (K : RingedSpace.ModuleDerived (Limits.pullback f g).toRingedSpace)
    (hK_coherent : DerivedCategory.cohomologyIn
      (SheafOfModules.isCoherent (Limits.pullback f g).toRingedSpace.ringCatSheaf) K)
    (hK_bounded : (t.bounded : ObjectProperty
      (RingedSpace.ModuleDerived (Limits.pullback f g).toRingedSpace)) K) :
    ∀ i : ℤ, Scheme.Modules.HasProperSupportOver
      (Limits.pullback.snd f g) (RingedSpace.ModuleDerived.cohomologySheaf K i) := sorry

/-- If the source morphism is proper, every coherent term of a bounded flat representative has
proper support over the target. -/
@[stacks 0FYU "proper support of representative terms"]
theorem representativeTerm_hasProperSupportOver_of_isProper
    {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    [IsNoetherian S] [Scheme.Hom.FiniteType f]
    [Scheme.Hom.FiniteType g] [IsProper f]
    (K : RingedSpace.ModuleDerived (Limits.pullback f g).toRingedSpace)
    (hK_coherent : DerivedCategory.cohomologyIn
      (SheafOfModules.isCoherent (Limits.pullback f g).toRingedSpace.ringCatSheaf) K)
    (hK_bounded : (t.bounded : ObjectProperty
      (RingedSpace.ModuleDerived (Limits.pullback f g).toRingedSpace)) K)
    (𝒦 : CochainComplex (Limits.pullback f g).toRingedSpace.Modules ℤ)
    (eK : DerivedCategory.Q.obj 𝒦 ≅ K)
    (h𝒦_bounded : CochainComplex.bounded
      (Limits.pullback f g).toRingedSpace.Modules 𝒦)
    [∀ i : ℤ, (𝒦.X i).IsCoherent]
    [∀ i : ℤ, SheafOfModules.IsFlatOver
      (𝒦.X i) (Limits.pullback.fst f g).toShHom] :
    ∀ i : ℤ, Scheme.Modules.HasProperSupportOver
      (Limits.pullback.snd f g) (𝒦.X i) := sorry

end AlgebraicGeometry.Scheme.FourierMukai
