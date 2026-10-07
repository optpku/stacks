module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Pullbacks
public import ReasLib.Algebra.Homology.CochainComplex.Bounded
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Perfect
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Perfect.Pullback
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.FourierMukai
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Pushforward.Perfect
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Pushforward.Perfect.Tensor
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.StructureSheaf
public import ReasLib.AlgebraicGeometry.Scheme.OverField
public import ReasLib.CategoryTheory.ObjectProperty.FullSubcategory.Restriction

@[expose] public section

open AlgebraicGeometry CategoryTheory
open DerivedCategory.TStructure

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.FourierMukai

/-- The ambient derived object underlying the diagonal kernel `Δ_* 𝒪_X`. -/
noncomputable def diagonalKernelUnderlying
    {k : Type u} [Field k] (X : SchemeOverField k) :
    RingedSpace.ModuleDerived
      (Limits.pullback X.hom X.hom).toRingedSpace :=
  (RingedSpace.moduleDerivedPushforward
      (Limits.pullback.diagonal X.hom).toShHom).obj
    (Scheme.DerivedQCoh.structureSheaf X.left).obj

/-- The derived diagonal pushforward of the structure sheaf of a smooth proper scheme over a
field is perfect. -/
theorem diagonalKernelUnderlying_isPerfect
    {k : Type u} [Field k] (X : SchemeOverField k) [Smooth X.hom]
    [IsProper X.hom] :
    RingedSpace.ModuleDerived.IsPerfect (diagonalKernelUnderlying X) := sorry

/-- The diagonal kernel as a perfect derived object on a smooth proper scheme over a field. -/
noncomputable def diagonalKernel
    {k : Type u} [Field k] (X : SchemeOverField k) [Smooth X.hom]
    [IsProper X.hom] :
    @RingedSpace.ModuleDerived.Perfect
      (Limits.pullback X.hom X.hom).toRingedSpace :=
  ⟨diagonalKernelUnderlying X, diagonalKernelUnderlying_isPerfect X⟩

/-- The underlying derived object of the perfect diagonal kernel on a smooth proper scheme is the
diagonal pushforward of the derived structure sheaf. -/
theorem diagonalKernel_obj
    {k : Type u} [Field k] (X : SchemeOverField k) [Smooth X.hom]
    [IsProper X.hom] :
    (diagonalKernel X).obj = diagonalKernelUnderlying X := sorry

/-- A perfect kernel on the self-product of a smooth proper scheme over a field induces an
ambient Fourier–Mukai functor preserving perfect objects. -/
theorem perfectSelfFunctor_mapsToPerfect
    {k : Type u} [Field k] (X : SchemeOverField k) [Smooth X.hom]
    [IsProper X.hom]
    (K : @RingedSpace.ModuleDerived.Perfect
      (Limits.pullback X.hom X.hom).toRingedSpace) :
    RingedSpace.ModuleDerived.perfect (X := X.left.toRingedSpace) ≤
      (RingedSpace.ModuleDerived.perfect (X := X.left.toRingedSpace)).inverseImage
        (functor X.hom X.hom K.obj) := sorry

/-- The Fourier–Mukai self-transform associated to a perfect kernel on the self-product of
a smooth proper scheme over a field, restricted to perfect objects. -/
noncomputable def perfectSelfFunctor
    {k : Type u} [Field k] (X : SchemeOverField k) [Smooth X.hom]
    [IsProper X.hom]
    (K : @RingedSpace.ModuleDerived.Perfect
      (Limits.pullback X.hom X.hom).toRingedSpace) :
    @RingedSpace.ModuleDerived.Perfect X.left.toRingedSpace ⥤
      @RingedSpace.ModuleDerived.Perfect X.left.toRingedSpace :=
  ObjectProperty.FullSubcategory.restrict
    (functor X.hom X.hom K.obj) (perfectSelfFunctor_mapsToPerfect X K)

/-- The restricted Fourier–Mukai self-transform agrees with the ambient transform after
inclusion of perfect objects. -/
noncomputable def perfectSelfFunctor_comp_inclusionIso
    {k : Type u} [Field k] (X : SchemeOverField k) [Smooth X.hom]
    [IsProper X.hom]
    (K : @RingedSpace.ModuleDerived.Perfect
      (Limits.pullback X.hom X.hom).toRingedSpace) :
    perfectSelfFunctor X K ⋙ RingedSpace.ModuleDerived.Perfect.ι ≅
      RingedSpace.ModuleDerived.Perfect.ι ⋙ functor X.hom X.hom K.obj :=
  ObjectProperty.FullSubcategory.restrict.compιIso
    (functor X.hom X.hom K.obj) (perfectSelfFunctor_mapsToPerfect X K)

/-- A perfect kernel on the self-product of a smooth proper scheme over a field whose
Fourier–Mukai self-transform is isomorphic to the identity is isomorphic to the diagonal
kernel. -/
theorem kernel_iso_diagonal_of_functor_iso_identity
    {k : Type u} [Field k] (X : SchemeOverField k)
    [Smooth X.hom] [IsProper X.hom]
    (K : @RingedSpace.ModuleDerived.Perfect
      (Limits.pullback X.hom X.hom).toRingedSpace)
    (hΦ : Nonempty
      (perfectSelfFunctor X K ≅
        𝟭 (@RingedSpace.ModuleDerived.Perfect X.left.toRingedSpace))) :
    Nonempty (K ≅ diagonalKernel X) := sorry

/-- Over a Noetherian base, finite-type structure morphisms and a bounded coherent kernel
with proper cohomological support over `Y` and finite Tor dimension over the inverse-image
structure sheaf of `Y` give a Fourier–Mukai transform preserving perfect objects. -/
theorem mapsPerfect_of_coherent_of_finiteTorDimension
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
        (Limits.pullback.snd f g).toShHom).obj K)) :
    ∀ M : RingedSpace.ModuleDerived X.toRingedSpace,
      RingedSpace.ModuleDerived.IsPerfect M →
        RingedSpace.ModuleDerived.IsPerfect ((FourierMukai.functor f g K).obj M) := sorry

/-- A Fourier–Mukai transform preserves perfect objects when `X ⟶ S` is of finite
presentation and its kernel has a bounded finitely presented, termwise `Y`-flat
representative with proper support over `Y`. -/
theorem mapsPerfect_of_flatRepresentative
    {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    [Scheme.Hom.FinitePresentation f]
    (K : RingedSpace.ModuleDerived (Limits.pullback f g).toRingedSpace)
    (Kmodel : CochainComplex (Limits.pullback f g).toRingedSpace.Modules ℤ)
    (eK : DerivedCategory.Q.obj Kmodel ≅ K)
    (hKmodel_bounded : CochainComplex.bounded
      (Limits.pullback f g).toRingedSpace.Modules Kmodel)
    [∀ i : ℤ, (Kmodel.X i).IsFinitePresentation]
    [∀ i : ℤ, SheafOfModules.IsFlatOver
      (Kmodel.X i) (Limits.pullback.snd f g).toShHom]
    [∀ i : ℤ, Scheme.Modules.HasProperSupportOver
      (Limits.pullback.snd f g) (Kmodel.X i)] :
    ∀ M : RingedSpace.ModuleDerived X.toRingedSpace,
      RingedSpace.ModuleDerived.IsPerfect M →
        RingedSpace.ModuleDerived.IsPerfect ((FourierMukai.functor f g K).obj M) := sorry

/-- A perfect kernel gives a Fourier–Mukai transform preserving perfect objects when
`X ⟶ S` is proper, flat, and of finite presentation. -/
theorem mapsPerfect_of_perfect_of_flat
    {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    [Scheme.Hom.FinitePresentation f] [Flat f] [IsProper f]
    (K : RingedSpace.ModuleDerived (Limits.pullback f g).toRingedSpace)
    (hK_perfect : RingedSpace.ModuleDerived.IsPerfect K) :
    ∀ M : RingedSpace.ModuleDerived X.toRingedSpace,
      RingedSpace.ModuleDerived.IsPerfect M →
        RingedSpace.ModuleDerived.IsPerfect ((FourierMukai.functor f g K).obj M) := sorry

/-- Over a Noetherian base, a perfect kernel gives a Fourier–Mukai transform preserving
perfect objects when `X ⟶ S` is flat and proper. -/
theorem mapsPerfect_of_noetherian_of_perfect
    {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    [IsNoetherian S] [Flat f] [IsProper f]
    (K : RingedSpace.ModuleDerived (Limits.pullback f g).toRingedSpace)
    (hK_perfect : RingedSpace.ModuleDerived.IsPerfect K) :
    ∀ M : RingedSpace.ModuleDerived X.toRingedSpace,
      RingedSpace.ModuleDerived.IsPerfect M →
        RingedSpace.ModuleDerived.IsPerfect ((FourierMukai.functor f g K).obj M) := sorry

/-- A kernel perfect over `Y` gives a Fourier–Mukai transform preserving perfect objects
when `X ⟶ S` is proper, flat, and of finite presentation. -/
theorem mapsPerfect_of_relativePerfect_of_flat
    {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    [Scheme.Hom.FinitePresentation f] [Flat f] [IsProper f]
    (K : RingedSpace.ModuleDerived (Limits.pullback f g).toRingedSpace)
    (hK_yPerfect : RingedSpace.ModuleDerived.IsPerfectOver
      (Limits.pullback.snd f g).toShHom K) :
    ∀ M : RingedSpace.ModuleDerived X.toRingedSpace,
      RingedSpace.ModuleDerived.IsPerfect M →
        RingedSpace.ModuleDerived.IsPerfect ((FourierMukai.functor f g K).obj M) := sorry

/-- Over a Noetherian base, a kernel perfect over `Y` gives a Fourier–Mukai transform
preserving perfect objects when `X ⟶ S` is flat and proper. -/
theorem mapsPerfect_of_noetherian_of_relativePerfect
    {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    [IsNoetherian S] [Flat f] [IsProper f]
    (K : RingedSpace.ModuleDerived (Limits.pullback f g).toRingedSpace)
    (hK_yPerfect : RingedSpace.ModuleDerived.IsPerfectOver
      (Limits.pullback.snd f g).toShHom K) :
    ∀ M : RingedSpace.ModuleDerived X.toRingedSpace,
      RingedSpace.ModuleDerived.IsPerfect M →
        RingedSpace.ModuleDerived.IsPerfect ((FourierMukai.functor f g K).obj M) := sorry

end AlgebraicGeometry.Scheme.FourierMukai
