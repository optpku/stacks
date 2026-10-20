/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Ample.Relative.Characterization
public import ReasLib.AlgebraicGeometry.Scheme.Module.Ample.RelativeVery
public import ReasLib.AlgebraicGeometry.Scheme.Module.RelativeProjFromSections.DegreeOne
public import ReasLib.AlgebraicGeometry.Scheme.RelativeProj.GeneratedByDegreeOne

/-!
# Criteria for relative very ampleness

This module compares relative very ampleness with its open-local form, with relative projective
section maps from algebras generated in degree one, and with the morphism classified by the
canonical pullback-pushforward counit.
-/

@[expose] public section

open CategoryTheory
open SheafOfModules.RingedSite
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry

section

variable {X S : Scheme.{u}} (f : X ⟶ S) (L : X.Modules)

/-- A module is relatively very ample on a base-open cover when its restriction to every
corresponding inverse-image open is relatively very ample. -/
def RelativelyVeryAmpleOnBaseOpenCover : Prop :=
  ∃ (ι : Type u) (V : ι → S.Opens), TopologicalSpace.IsOpenCover V ∧
    ∀ i : ι, RelativelyVeryAmple.onBasePreimage f L (V i)

/-- A morphism to the projective bundle of a pushforward module is canonical when it underlies
a lift classified by the invertible quotient given by the pullback-pushforward counit. -/
def IsCanonicalPushforwardMap
    {P : Scheme.{u}} {π : P ⟶ S}
    [hL : Scheme.Modules.Invertible L]
    (hπ : Scheme.ProjectiveBundle.Representation π
      ((Scheme.Modules.pushforward f).obj L))
    (hcounit : Epi
      ((Scheme.Modules.pullbackPushforwardAdjunction f).counit.app L))
    (φ : X ⟶ P) : Prop :=
  ∃ lift : Scheme.ProjectiveBundle.Lift π f,
    lift.hom = φ ∧
      hπ.liftEquiv f lift =
        { object := L
          isInvertible := hL
          hom := (Scheme.Modules.pullbackPushforwardAdjunction f).counit.app L
          hom_epi := hcounit }

/-- The canonical pushforward-map relation is exactly the existence of a lift with the stated
underlying morphism and pullback-pushforward quotient. -/
theorem isCanonicalPushforwardMap_iff
    {P : Scheme.{u}} {π : P ⟶ S}
    [hL : Scheme.Modules.Invertible L]
    (hπ : Scheme.ProjectiveBundle.Representation π
      ((Scheme.Modules.pushforward f).obj L))
    (hcounit : Epi
      ((Scheme.Modules.pullbackPushforwardAdjunction f).counit.app L))
    (φ : X ⟶ P) :
    IsCanonicalPushforwardMap f L hπ hcounit φ ↔
      ∃ lift : Scheme.ProjectiveBundle.Lift π f,
        lift.hom = φ ∧
          hπ.liftEquiv f lift =
            { object := L
              isInvertible := hL
              hom := (Scheme.Modules.pullbackPushforwardAdjunction f).counit.app L
              hom_epi := hcounit } :=
  Iff.rfl

/-- The canonical pushforward criterion holds when the morphism is quasi-separated, its
pullback-pushforward counit is epic, and the projective-bundle morphism classified by that
quotient is an immersion. -/
def HasCanonicalPushforwardImmersion
    [Scheme.Modules.Invertible L] : Prop :=
  QuasiSeparated f ∧
    ∃ hcounit : Epi
        ((Scheme.Modules.pullbackPushforwardAdjunction f).counit.app L),
      ∃ (P : Scheme.{u}) (π : P ⟶ S)
        (hπ : Scheme.ProjectiveBundle.Representation π
          ((Scheme.Modules.pushforward f).obj L)),
        ∃ φ : X ⟶ P,
          IsCanonicalPushforwardMap f L hπ hcounit φ ∧ IsImmersion φ

/-- The degree-one relative-projective criterion holds when a commutative graded algebra sheaf
is affine-locally generated in degree one and its multiplicative section homomorphism has epic
adjoint degree-one map and an immersive canonical full-source relative projective map. -/
def HasDegreeOneGeneratedImmersionRelativeProjSectionMap
    [hL : Scheme.Modules.Invertible L] : Prop :=
  ∃ (𝒜 : GradedAlgebraSheaf.{u, u} S.sheaf) (hcomm : 𝒜.IsCommutative),
    GradedAlgebraSheaf.GeneratedByDegreeOne 𝒜 ∧
      HasRelativeProjSectionMapWith f L 𝒜 @IsImmersion
        (fun ψ ↦ Scheme.RelativeProjTwist.Hom.HasEpicDegreeOneAdjoint ψ)
        (hL := hL) (hcomm := hcomm)

/-- Relative very ampleness implies relative very ampleness after restriction to the members
of a suitable base-open cover. -/
theorem relativelyVeryAmpleOnBaseOpenCover_of_relativelyVeryAmple
    [Scheme.Modules.Invertible L]
    (hL : RelativelyVeryAmple f L) :
    RelativelyVeryAmpleOnBaseOpenCover f L := sorry

/-- For a quasi-compact morphism, relative very ampleness on a base-open cover implies the
canonical pushforward immersion criterion. -/
theorem hasCanonicalPushforwardImmersion_of_relativelyVeryAmpleOnBaseOpenCover
    [QuasiCompact f] [Scheme.Modules.Invertible L]
    (hL : RelativelyVeryAmpleOnBaseOpenCover f L) :
    HasCanonicalPushforwardImmersion f L := sorry

/-- The canonical pushforward immersion criterion implies relative very ampleness. -/
theorem relativelyVeryAmple_of_hasCanonicalPushforwardImmersion
    [Scheme.Modules.Invertible L]
    (hL : HasCanonicalPushforwardImmersion f L) :
    RelativelyVeryAmple f L := sorry

namespace HasCanonicalPushforwardImmersion

/-- A canonical pushforward immersion supplies a degree-one-generated relative projective
section-map presentation. -/
theorem hasDegreeOnePresentation
    [Scheme.Modules.Invertible L]
    (hL : HasCanonicalPushforwardImmersion f L) :
    HasDegreeOneGeneratedImmersionRelativeProjSectionMap f L := sorry

end HasCanonicalPushforwardImmersion

namespace DegreeOnePresentation

/-- A degree-one-generated relative projective section-map presentation with immersive
associated map implies relative very ampleness. -/
theorem relativelyVeryAmple
    [Scheme.Modules.Invertible L]
    (hL : HasDegreeOneGeneratedImmersionRelativeProjSectionMap f L) :
    RelativelyVeryAmple f L := sorry

end DegreeOnePresentation

/-- For a quasi-compact morphism and an invertible module, relative very ampleness, its
base-open-local form, the degree-one-generated relative-projective criterion, and the canonical
pushforward immersion criterion are equivalent. -/
theorem relativelyVeryAmple_tfae
    [QuasiCompact f] [Scheme.Modules.Invertible L] :
    List.TFAE [
      RelativelyVeryAmple f L,
      RelativelyVeryAmpleOnBaseOpenCover f L,
      HasDegreeOneGeneratedImmersionRelativeProjSectionMap f L,
      HasCanonicalPushforwardImmersion f L] := by
  tfae_have 1 → 2 := relativelyVeryAmpleOnBaseOpenCover_of_relativelyVeryAmple f L
  tfae_have 2 → 4 :=
    hasCanonicalPushforwardImmersion_of_relativelyVeryAmpleOnBaseOpenCover f L
  tfae_have 4 → 1 := relativelyVeryAmple_of_hasCanonicalPushforwardImmersion f L
  tfae_have 4 → 3 :=
    HasCanonicalPushforwardImmersion.hasDegreeOnePresentation f L
  tfae_have 3 → 1 :=
    DegreeOnePresentation.relativelyVeryAmple f L
  tfae_finish

end

end AlgebraicGeometry
