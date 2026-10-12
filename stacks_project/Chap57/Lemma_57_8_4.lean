/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Perfect.FourierMukai

@[expose] public section

open AlgebraicGeometry CategoryTheory
open DerivedCategory.TStructure

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.FourierMukai

/- Lemma 57.8.4 (1): under Noetherian and finite-type hypotheses, a bounded coherent
kernel with proper cohomological support over `Y` and finite Tor dimension over the
inverse-image structure sheaf of `Y` sends perfect complexes on `X` to perfect complexes on `Y`.
-/
@[stacks 0FYT]
#check (AlgebraicGeometry.Scheme.FourierMukai.mapsPerfect_of_coherent_of_finiteTorDimension :
    ∀ {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
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
        (Limits.pullback.snd f g).toShHom).obj K)),
    ∀ M : RingedSpace.ModuleDerived X.toRingedSpace,
      RingedSpace.ModuleDerived.IsPerfect M →
        RingedSpace.ModuleDerived.IsPerfect ((FourierMukai.functor f g K).obj M))

/- Lemma 57.8.4 (2): if `X ⟶ S` is of finite presentation and the kernel has a bounded
finitely presented, termwise `Y`-flat representative with proper support over `Y`, then
the Fourier--Mukai functor sends perfect complexes on `X` to perfect complexes on `Y`.
-/
@[stacks 0FYT]
#check (AlgebraicGeometry.Scheme.FourierMukai.mapsPerfect_of_flatRepresentative :
    ∀ {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
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
      (Limits.pullback.snd f g) (Kmodel.X i)],
    ∀ M : RingedSpace.ModuleDerived X.toRingedSpace,
      RingedSpace.ModuleDerived.IsPerfect M →
        RingedSpace.ModuleDerived.IsPerfect ((FourierMukai.functor f g K).obj M))

/- Lemma 57.8.4 (3): if `X ⟶ S` is proper, flat, and of finite presentation and the
kernel is perfect, then the Fourier--Mukai functor sends perfect complexes on `X` to
perfect complexes on `Y`.
-/
@[stacks 0FYT]
#check (AlgebraicGeometry.Scheme.FourierMukai.mapsPerfect_of_perfect_of_flat :
    ∀ {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    [Scheme.Hom.FinitePresentation f] [Flat f] [IsProper f]
    (K : RingedSpace.ModuleDerived (Limits.pullback f g).toRingedSpace)
    (hK_perfect : RingedSpace.ModuleDerived.IsPerfect K),
    ∀ M : RingedSpace.ModuleDerived X.toRingedSpace,
      RingedSpace.ModuleDerived.IsPerfect M →
        RingedSpace.ModuleDerived.IsPerfect ((FourierMukai.functor f g K).obj M))

/- Lemma 57.8.4 (4): if `S` is Noetherian, `X ⟶ S` is flat and proper, and the kernel
is perfect, then the Fourier--Mukai functor sends perfect complexes on `X` to perfect
complexes on `Y`.
-/
@[stacks 0FYT]
#check (AlgebraicGeometry.Scheme.FourierMukai.mapsPerfect_of_noetherian_of_perfect :
    ∀ {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    [IsNoetherian S] [Flat f] [IsProper f]
    (K : RingedSpace.ModuleDerived (Limits.pullback f g).toRingedSpace)
    (hK_perfect : RingedSpace.ModuleDerived.IsPerfect K),
    ∀ M : RingedSpace.ModuleDerived X.toRingedSpace,
      RingedSpace.ModuleDerived.IsPerfect M →
        RingedSpace.ModuleDerived.IsPerfect ((FourierMukai.functor f g K).obj M))

/- Lemma 57.8.4 (5): if `X ⟶ S` is proper, flat, and of finite presentation and the
kernel is perfect over `Y`, then the Fourier--Mukai functor sends perfect complexes on
`X` to perfect complexes on `Y`.
-/
@[stacks 0FYT]
#check (AlgebraicGeometry.Scheme.FourierMukai.mapsPerfect_of_relativePerfect_of_flat :
    ∀ {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    [Scheme.Hom.FinitePresentation f] [Flat f] [IsProper f]
    (K : RingedSpace.ModuleDerived (Limits.pullback f g).toRingedSpace)
    (hK_yPerfect : RingedSpace.ModuleDerived.IsPerfectOver
      (Limits.pullback.snd f g).toShHom K),
    ∀ M : RingedSpace.ModuleDerived X.toRingedSpace,
      RingedSpace.ModuleDerived.IsPerfect M →
        RingedSpace.ModuleDerived.IsPerfect ((FourierMukai.functor f g K).obj M))

/- Lemma 57.8.4 (6): if `S` is Noetherian, `X ⟶ S` is flat and proper, and the kernel
is perfect over `Y`, then the Fourier--Mukai functor sends perfect complexes on `X` to
perfect complexes on `Y`.
-/
@[stacks 0FYT]
#check (AlgebraicGeometry.Scheme.FourierMukai.mapsPerfect_of_noetherian_of_relativePerfect :
    ∀ {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    [IsNoetherian S] [Flat f] [IsProper f]
    (K : RingedSpace.ModuleDerived (Limits.pullback f g).toRingedSpace)
    (hK_yPerfect : RingedSpace.ModuleDerived.IsPerfectOver
      (Limits.pullback.snd f g).toShHom K),
    ∀ M : RingedSpace.ModuleDerived X.toRingedSpace,
      RingedSpace.ModuleDerived.IsPerfect M →
        RingedSpace.ModuleDerived.IsPerfect ((FourierMukai.functor f g K).obj M))

end AlgebraicGeometry.Scheme.FourierMukai
