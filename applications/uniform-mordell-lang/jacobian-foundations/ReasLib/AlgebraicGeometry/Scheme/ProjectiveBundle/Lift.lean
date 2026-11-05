module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Lifts through projective-bundle morphisms

This leaf owns the concrete data of a morphism over the base of a projective
bundle. It is independent of the quotient representation property.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme.ProjectiveBundle

variable {X P : Scheme.{u}}

/-- A lift of `f` through `π`, together with its specified triangle over the base. -/
@[stacks 01OB "lift through a projective-bundle morphism"]
structure Lift {T : Scheme.{u}} (π : P ⟶ X) (f : T ⟶ X) where
  /-- The morphism into the total space. -/
  hom : T ⟶ P
  /-- The triangle over the base commutes. -/
  fac : hom ≫ π = f

namespace Lift

/-- Precomposing a lift by a morphism of test schemes gives the induced lift over the composite
base morphism. -/
def precomp {S T : Scheme.{u}} {π : P ⟶ X} {f : T ⟶ X}
    (σ : Lift π f) (g : S ⟶ T) : Lift π (g ≫ f) where
  hom := g ≫ σ.hom
  fac := by rw [Category.assoc, σ.fac]

/-- A lift determines the canonical section of the projective bundle obtained by base change to
its source. -/
noncomputable def baseChangeSection {T : Scheme.{u}} {π : P ⟶ X} {f : T ⟶ X}
    (σ : Lift π f) : T ⟶ pullback π f :=
  pullback.lift σ.hom (𝟙 T) (by simpa using σ.fac)

/-- The sections of successive base changes form the canonical commutative square. -/
theorem baseChangeSection_precomp {S T : Scheme.{u}} {π : P ⟶ X} {f : T ⟶ X}
    (σ : Lift π f) (g : S ⟶ T) :
    (precomp σ g).baseChangeSection ≫
        pullback.lift (pullback.fst π (g ≫ f))
          (pullback.snd π (g ≫ f) ≫ g)
          (by simpa [Category.assoc] using pullback.condition (f := π) (g := g ≫ f)) =
      g ≫ σ.baseChangeSection := sorry

/-- The identity morphism satisfies the triangle required for the identity lift. -/
@[stacks 01OB "identity lift triangle"]
theorem identity_fac (π : P ⟶ X) :
    𝟙 P ≫ π = π := sorry

/-- The canonical identity lift of a projective-bundle morphism along its own base map. -/
@[stacks 01OB "identity lift of a projective-bundle morphism"]
def identity (π : P ⟶ X) : Lift π π :=
  ⟨𝟙 P, identity_fac π⟩

/-- The morphism of the identity lift is the identity morphism. -/
@[simp, stacks 01OB "identity lift morphism"]
theorem identity_hom (π : P ⟶ X) :
    (identity π).hom = 𝟙 P := sorry

/-- Pullback first along the base morphism and then along a lift agrees with pullback along the
specified source morphism of the lift. -/
noncomputable def pullbackSourceIso {T : Scheme.{u}} {π : P ⟶ X} {f : T ⟶ X}
    (σ : Lift π f) (ℰ : X.Modules) :
    (Scheme.Modules.pullback σ.hom).obj ((Scheme.Modules.pullback π).obj ℰ) ≅
      (Scheme.Modules.pullback f).obj ℰ :=
  (Scheme.Modules.pullbackComp σ.hom π).app ℰ ≪≫
    (Scheme.Modules.pullbackCongr σ.fac).app ℰ

end Lift

/-- Lifts through a fixed projective-bundle morphism are determined by their morphism into the
total space. -/
@[ext]
theorem Lift.ext {T : Scheme.{u}} {π : P ⟶ X} {f : T ⟶ X}
    (a b : Lift π f) (h : a.hom = b.hom) :
    a = b := sorry

end AlgebraicGeometry.Scheme.ProjectiveBundle
