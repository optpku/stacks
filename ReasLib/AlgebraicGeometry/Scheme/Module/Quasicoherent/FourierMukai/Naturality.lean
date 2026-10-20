/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Quasicoherent.FourierMukai
public import ReasLib.CategoryTheory.ObjectProperty.FullSubcategory.Restriction.Naturality
public import Mathlib.CategoryTheory.Monoidal.Category

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open CategoryTheory.ObjectProperty
open AlgebraicGeometry
open AlgebraicGeometry.Scheme

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.QCoh

/-- A morphism of kernels induces a natural transformation of tensor-by-kernel
functors on quasicoherent modules. -/
def tensorRightHom {P : Scheme.{u}} {K K' : Scheme.QCoh P} (α : K ⟶ K') :
    tensorRight K ⟶ tensorRight K' :=
  FullSubcategory.restrict.natTrans
    (tensorRightPreservesQuasiCoherent K)
    (tensorRightPreservesQuasiCoherent K')
    ((curriedTensor P.Modules).flip.map α.hom)

/-- A morphism of kernels induces a natural transformation of their
Fourier--Mukai functors. -/
def fourierMukaiHom
    {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    [QuasiCompact (Limits.pullback.snd f g)]
    [QuasiSeparated (Limits.pullback.snd f g)]
    {K K' : Scheme.QCoh (Limits.pullback f g)} (α : K ⟶ K') :
    fourierMukai f g K ⟶ fourierMukai f g K' :=
  Functor.whiskerLeft (Scheme.QCoh.pullback (Limits.pullback.fst f g))
    (Functor.whiskerRight (tensorRightHom α)
      (Scheme.QCoh.pushforward (Limits.pullback.snd f g)))

/-- The Fourier--Mukai transformation associated to an identity kernel map is
the identity natural transformation. -/
theorem fourierMukaiHom_id
    {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    [QuasiCompact (Limits.pullback.snd f g)]
    [QuasiSeparated (Limits.pullback.snd f g)] (K : Scheme.QCoh (Limits.pullback f g)) :
    fourierMukaiHom f g (𝟙 K) = 𝟙 (fourierMukai f g K) := sorry

/-- Fourier--Mukai transformations compose according to composition of kernel
morphisms. -/
theorem fourierMukaiHom_comp
    {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    [QuasiCompact (Limits.pullback.snd f g)]
    [QuasiSeparated (Limits.pullback.snd f g)]
    {K K' K'' : Scheme.QCoh (Limits.pullback f g)}
    (α : K ⟶ K') (β : K' ⟶ K'') :
    fourierMukaiHom f g (α ≫ β) =
      fourierMukaiHom f g α ≫ fourierMukaiHom f g β := sorry

end AlgebraicGeometry.Scheme.QCoh
