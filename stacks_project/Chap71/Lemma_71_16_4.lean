/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ProjectiveBundle.Conormal
import StacksCheckRecall

/-! # Lemma 71.16.4 -/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.InvertibleQuotient
open AlgebraicGeometry.AlgebraicSpace.ProjectiveBundle
open AlgebraicGeometry.AlgebraicSpace.ProjectiveBundle.SymmetricPresentation
open AlgebraicGeometry.AlgebraicSpace

universe u

/- Lemma 71.16.4: sections, invertible quotient classes, conormal comparison, and base change. -/
@[stacks 0B4I] #check (AlgebraicGeometry.AlgebraicSpace.ProjectiveBundle.SymmetricPresentation.sectionToQuotientClass_bijective :
  ∀ {S : Scheme.{u}} {X P : AlgebraicSpace S} {ℰ : X.Modules} [ℰ.IsQuasicoherent]
    {π : P ⟶ X} (Pres : SymmetricPresentation π ℰ),
    Function.Bijective Pres.sectionToQuotientClass)

#check (AlgebraicGeometry.AlgebraicSpace.ProjectiveBundle.SymmetricPresentation.liftToQuotientClass_naturality :
  ∀ {S : Scheme.{u}} {X P : AlgebraicSpace S} {ℰ : X.Modules} [ℰ.IsQuasicoherent]
    {π : P ⟶ X} (Pres : SymmetricPresentation π ℰ)
    {T R : AlgebraicSpace S} (f : T ⟶ X) (σ : Lift π f) (g : R ⟶ T),
    Pres.liftToQuotientClass (g ≫ f) (σ.precomp g) =
      quotientPointMap f g (Pres.liftToQuotientClass f σ))

#check (AlgebraicGeometry.AlgebraicSpace.ProjectiveBundle.SymmetricPresentation.section_isClosedImmersion :
  ∀ {S : Scheme.{u}} {X P : AlgebraicSpace S} {ℰ : X.Modules} [ℰ.IsQuasicoherent]
    {π : P ⟶ X} (Pres : SymmetricPresentation π ℰ) (σ : Lift π (𝟙 X)),
    IsClosedImmersion σ.hom)

#check (AlgebraicGeometry.AlgebraicSpace.ProjectiveBundle.SymmetricPresentation.sectionConormalMap :
  ∀ {S : Scheme.{u}} {X P : AlgebraicSpace S} {ℰ : X.Modules} [ℰ.IsQuasicoherent]
    {π : P ⟶ X} (Pres : SymmetricPresentation π ℰ)
    (σ : Lift π (𝟙 X)) (q : InvertibleQuotient ℰ)
    (h : IsoClass.mk q = Pres.sectionToQuotientClass σ),
    conormalObject q ⟶ Pres.sectionConormalSheaf σ)

#check (AlgebraicGeometry.AlgebraicSpace.ProjectiveBundle.SymmetricPresentation.sectionConormalMap_isIso :
  ∀ {S : Scheme.{u}} {X P : AlgebraicSpace S} {ℰ : X.Modules} [ℰ.IsQuasicoherent]
    {π : P ⟶ X} (Pres : SymmetricPresentation π ℰ)
    (σ : Lift π (𝟙 X)) (q : InvertibleQuotient ℰ)
    (h : IsoClass.mk q = Pres.sectionToQuotientClass σ),
    IsIso (sectionConormalMap Pres σ q h))

#check (AlgebraicGeometry.AlgebraicSpace.ProjectiveBundle.SymmetricPresentation.liftConormalMap_precomp :
  ∀ {S : Scheme.{u}} {X P : AlgebraicSpace S} {ℰ : X.Modules} [ℰ.IsQuasicoherent]
    {π : P ⟶ X} (Pres : SymmetricPresentation π ℰ)
    {T R : AlgebraicSpace S} (f : T ⟶ X) (σ : Lift π f) (g : R ⟶ T)
    (q : InvertibleQuotient ((Modules.pullback f).obj ℰ))
    (h : IsoClass.mk q = IsoClass.mk (Pres.liftSourceQuotient σ)),
    (Modules.pullback g).map (Pres.liftConormalMap σ q h) ≫
        Pres.precompConormalSheafMap σ g =
      liftConormalPullbackComparison g q ≫
        Pres.liftConormalMap (σ.precomp g) (pullbackRepresentative g q)
          (Pres.pullbackRepresentative_class σ g q h))
