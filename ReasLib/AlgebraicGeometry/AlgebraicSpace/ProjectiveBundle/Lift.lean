/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Pullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Pullback

/-!
# Lifts through projective-bundle morphisms of algebraic spaces

This leaf owns the concrete data of a morphism over the base of a relative
projective bundle of algebraic spaces.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.ProjectiveBundle

variable {S : Scheme.{u}} {X P : AlgebraicSpace S}

/-- A lift of `f` through `π`, together with its specified triangle over the base. -/
structure Lift {T : AlgebraicSpace S} (π : P ⟶ X) (f : T ⟶ X) where
  /-- The morphism into the total space. -/
  hom : T ⟶ P
  /-- The triangle over the base commutes. -/
  fac : hom ≫ π = f

namespace Lift

/-- Construct a lift from a morphism into the total space and a commuting triangle. -/
def of {T : AlgebraicSpace S} {π : P ⟶ X} {f : T ⟶ X}
    (hom : T ⟶ P) (fac : hom ≫ π = f) : Lift π f :=
  ⟨hom, fac⟩

/-- Precomposing a lift by a morphism of test algebraic spaces gives the induced lift over
the composite base morphism. -/
def precomp {R T : AlgebraicSpace S} {π : P ⟶ X} {f : T ⟶ X}
    (σ : Lift π f) (g : R ⟶ T) : Lift π (g ≫ f) where
  hom := g ≫ σ.hom
  fac := (Category.assoc g σ.hom π).trans (congrArg (fun x ↦ g ≫ x) σ.fac)

/-- A lift determines the canonical section of the projective bundle obtained by base change
to its source. -/
def baseChangeSection {T : AlgebraicSpace S} {π : P ⟶ X} {f : T ⟶ X}
    (σ : Lift π f) : T ⟶ pullback π f :=
  pullback.lift σ.hom (𝟙 T) (σ.fac.trans (Category.id_comp f).symm)

/-- The sections of successive base changes form the canonical commutative square. -/
theorem baseChangeSection_precomp {R T : AlgebraicSpace S} {π : P ⟶ X} {f : T ⟶ X}
    (σ : Lift π f) (g : R ⟶ T) :
    (precomp σ g).baseChangeSection ≫
        pullback.lift (pullback.fst π (g ≫ f))
          (pullback.snd π (g ≫ f) ≫ g)
          ((pullback.condition (f := π) (g := g ≫ f)).trans
            (Category.assoc (pullback.snd π (g ≫ f)) g f).symm) =
      g ≫ σ.baseChangeSection := sorry

/-- The canonical identity lift of a projective-bundle morphism along its own base map. -/
def identity (π : P ⟶ X) : Lift π π :=
  ⟨𝟙 P, Category.id_comp π⟩

/-- The morphism of the identity lift is the identity morphism. -/
@[simp]
theorem identity_hom (π : P ⟶ X) :
    (identity π).hom = 𝟙 P := rfl

/-- Pullback first along the structure morphism and then along a lift agrees with pullback
along the specified source morphism of the lift. -/
def pullbackSourceIso {T : AlgebraicSpace S} {π : P ⟶ X} {f : T ⟶ X}
    (σ : Lift π f) (ℰ : X.Modules) :
    (Modules.pullback σ.hom).obj ((Modules.pullback π).obj ℰ) ≅
      (Modules.pullback f).obj ℰ :=
  (Modules.pullbackCompIso σ.hom π).app ℰ ≪≫
    eqToIso (congrArg (fun h ↦ (Modules.pullback h).obj ℰ) σ.fac)

end Lift

/-- Lifts through a fixed projective-bundle morphism are determined by their morphism into
the total space. -/
@[ext]
theorem Lift.ext {T : AlgebraicSpace S} {π : P ⟶ X} {f : T ⟶ X}
    (a b : Lift π f) (h : a.hom = b.hom) :
    a = b := sorry

/-- The commuting triangle of a lift. -/
theorem Lift.fac_spec {T : AlgebraicSpace S} {π : P ⟶ X} {f : T ⟶ X}
    (σ : Lift π f) :
    σ.hom ≫ π = f := σ.fac

end AlgebraicGeometry.AlgebraicSpace.ProjectiveBundle
