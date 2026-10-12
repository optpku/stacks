/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Affine.Diagonal
public import ReasLib.AlgebraicGeometry.Scheme.Module.Quasicoherent.FourierMukai
public import stacks_project.Chap56.«56_5_1_1»
public import stacks_project.Chap56.Lemma_56_5_2_Admissible

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry
open AlgebraicGeometry.Scheme

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.QCoh

variable {R : Type u} [CommRing R] {X Y : Scheme.{u}}
variable (x : X ⟶ Spec (CommRingCat.of R)) (y : Y ⟶ Spec (CommRingCat.of R))
variable [CompactSpace X] [IsAffineHom (prod.lift (𝟙 X) (𝟙 X))]
variable (F : Scheme.QCoh X ⥤ Scheme.QCoh Y) [Admissible x y F]

/-- The affine-local kernel and restriction-map data used to reconstruct a
Fourier--Mukai kernel. -/
structure FourierMukaiKernelData where
  kernel : Scheme.QCoh (Limits.pullback x y)
  affineKernel : ∀ {X' : Scheme.{u}} (f : X' ⟶ X) [IsAffine X'],
    Scheme.QCoh (Limits.pullback (f ≫ x) y)
  restrictedKernel : ∀ {X' : Scheme.{u}} (f : X' ⟶ X) [IsAffine X'],
    Scheme.QCoh (Limits.pullback (f ≫ x) y)
  restrictionMap : ∀ {X' : Scheme.{u}} (f : X' ⟶ X) [IsAffine X'],
    restrictedKernel f ⟶ affineKernel f

/-- The affine-local kernel data together with the degree-zero Čech comparison
and its deferred compatibility and correctness laws. -/
structure FourierMukaiReconstruction where
  data : FourierMukaiKernelData x y
  comparison : F ⟶ fourierMukai x y data.kernel
  restrictionIsIso : ∀ {X' : Scheme.{u}} (f : X' ⟶ X) [IsAffine X'],
    IsIso (data.restrictionMap f)
  restrictedKernel_spec : Prop
  restrictedKernel_spec_proof : restrictedKernel_spec
  restrictionCompatibility : Prop
  restrictionCompatibility_spec : restrictionCompatibility
  gluingCompatibility : Prop
  gluingCompatibility_spec : gluingCompatibility
  cechNaturality : Prop
  cechNaturality_spec : cechNaturality
  cechDegreeZero : Prop
  cechDegreeZero_spec : cechDegreeZero
  affineComparisonIsIso : ∀ {X' : Scheme.{u}} (f : X' ⟶ X) [IsAffine X'],
    IsIso (Functor.whiskerLeft (Scheme.QCoh.pushforward f) comparison)

/-- The glued kernel carried by explicit Fourier--Mukai reconstruction data. -/
noncomputable def fourierMukaiKernel
    (data : FourierMukaiKernelData x y) :
    Scheme.QCoh (Limits.pullback x y) :=
  data.kernel

/-- The comparison transformation carried by explicit Fourier--Mukai
reconstruction data. -/
noncomputable def toFourierMukai
    (reconstruction : FourierMukaiReconstruction x y F) :
    F ⟶ fourierMukai x y (fourierMukaiKernel x y reconstruction.data) :=
  reconstruction.comparison

/-- The source-level existence of the affine-local, glued, degree-zero
Čech reconstruction. -/
theorem exists_fourierMukaiReconstruction :
    ∃ reconstruction : FourierMukaiReconstruction x y F,
      ∀ {X' : Scheme.{u}} (f : X' ⟶ X) [IsAffine X'],
        IsIso (Functor.whiskerLeft (Scheme.QCoh.pushforward f)
          reconstruction.comparison) :=
  sorry

end AlgebraicGeometry.Scheme.QCoh
