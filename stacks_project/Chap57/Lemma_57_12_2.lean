/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType
public import stacks_project.Chap57.Lemma_57_12_2_FourierMukai

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.FourierMukai

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.FourierMukai

variable {k : Type u} [Field k] {X Y : Scheme.{u}}
variable (x : X ⟶ Spec (CommRingCat.of k)) (y : Y ⟶ Spec (CommRingCat.of k))
variable [x.FiniteType] [y.FiniteType] [IsSeparated x]
variable [IsNoetherian X]
variable [QuasiCompact (Limits.pullback.snd x y)]
variable [QuasiSeparated (Limits.pullback.snd x y)]
variable [Abelian (RingedSpace.Coh X.toRingedSpace)]
variable [Abelian (RingedSpace.Coh Y.toRingedSpace)]
variable [HasDerivedCategory.{u} (RingedSpace.Coh X.toRingedSpace)]
variable [HasDerivedCategory.{u} (RingedSpace.Coh Y.toRingedSpace)]
variable [Linear k (DerivedCategory.Bounded (RingedSpace.Coh X.toRingedSpace))]
variable [Linear k (DerivedCategory.Bounded (RingedSpace.Coh Y.toRingedSpace))]

/-- Lemma 57.12.2: if `k` is a field and `X`, `Y` are finite-type schemes over `k`
with `X` separated, then every `k`-linear exact functor
`F : DerivedCategory.Bounded (RingedSpace.Coh X.toRingedSpace) ⥤
DerivedCategory.Bounded (RingedSpace.Coh Y.toRingedSpace)` that sends the heart
`RingedSpace.Coh X.toRingedSpace` into `RingedSpace.Coh Y.toRingedSpace` admits a
sibling Fourier--Mukai functor `boundedCoherentFunctor x y K` whose kernel `K` is
a coherent module on `Limits.pullback x y`, flat over `X`, and with support
finite over `Y`. -/
@[stacks 0G00]
theorem exists_sibling_coherentFourierMukai
    (F : DerivedCategory.Bounded (RingedSpace.Coh X.toRingedSpace) ⥤
      DerivedCategory.Bounded (RingedSpace.Coh Y.toRingedSpace))
    [F.Linear k] [F.CommShift ℤ] [F.IsTriangulated]
    (hF : mapsHeartToHeart F) :
    ∃ (K : (Limits.pullback x y).Modules)
      (_ : IsCoherentFourierMukaiKernel x y K),
      Functor.areSiblings F (boundedCoherentFunctor x y K) := sorry

/-- There exists a coherent Fourier--Mukai kernel witnessing Lemma 57.12.2. -/
theorem exists_sibling_coherentFourierMukai.kernel
    (F : DerivedCategory.Bounded (RingedSpace.Coh X.toRingedSpace) ⥤
      DerivedCategory.Bounded (RingedSpace.Coh Y.toRingedSpace))
    [F.Linear k] [F.CommShift ℤ] [F.IsTriangulated]
    (hF : mapsHeartToHeart F) :
    ∃ K : (Limits.pullback x y).Modules, IsCoherentFourierMukaiKernel x y K := sorry

end AlgebraicGeometry.Scheme.FourierMukai
