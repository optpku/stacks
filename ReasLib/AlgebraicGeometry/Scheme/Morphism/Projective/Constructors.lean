/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Projective.Basic
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Constructors for projective scheme morphisms

This file packages the presentation data most often available in applications into the three
projective-morphism properties, avoiding repeated construction of nested existential witnesses.
-/

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry

/-- A finite-type quasi-coherent projective-bundle presentation constructs a projective morphism. -/
@[stacks 01W8 "projective morphism from a projective-bundle presentation"]
theorem Projective.of_presentation
    {X S P : Scheme.{u}} {f : X ⟶ S} {π : P ⟶ S} (ℰ : S.Modules)
    (hfinite : ℰ.IsFiniteType) (hquasicoherent : ℰ.IsQuasicoherent)
    (hπ : Scheme.ProjectiveBundle.Representation π ℰ) {i : X ⟶ P}
    (hi : ProjectivePresentation f π i) :
    Projective f := sorry

/-- A closed immersion over the base into a finite-type quasi-coherent projective bundle
constructs a projective morphism. -/
@[stacks 01W8 "projective morphism from a closed immersion"]
theorem Projective.of_closedImmersion
    {X S P : Scheme.{u}} {f : X ⟶ S} {π : P ⟶ S} (ℰ : S.Modules)
    (hfinite : ℰ.IsFiniteType) (hquasicoherent : ℰ.IsQuasicoherent)
    (hπ : Scheme.ProjectiveBundle.Representation π ℰ) {i : X ⟶ P}
    (hi : IsClosedImmersion i) (hcomm : i ≫ π = f) :
    Projective f := sorry

/-- A closed-immersion presentation into a chosen relative projective space constructs an
H-projective morphism. -/
@[stacks 01W8 "H-projective morphism from a presentation"]
theorem HProjective.of_presentation
    {X S : Scheme.{u}} {f : X ⟶ S} {n : ℕ}
    (P : ProjectiveSpaceOver S n) {i : X ⟶ P.scheme}
    (hi : ProjectivePresentation f P.hom i) :
    HProjective f := sorry

/-- A closed immersion over the base into a relative projective space constructs an H-projective
morphism. -/
@[stacks 01W8 "H-projective morphism from a closed immersion"]
theorem HProjective.of_closedImmersion
    {X S : Scheme.{u}} {f : X ⟶ S} {n : ℕ}
    (P : ProjectiveSpaceOver S n) {i : X ⟶ P.scheme}
    (hi : IsClosedImmersion i) (hcomm : i ≫ P.hom = f) :
    HProjective f := sorry

/-- Projectivity on every member of a target open cover constructs a locally projective morphism. -/
@[stacks 01W8 "locally projective morphism from an open cover"]
theorem LocallyProjective.of_openCover
    {X S : Scheme.{u}} {f : X ⟶ S} (𝒰 : Scheme.OpenCover.{u} S)
    (h𝒰 : ∀ i : 𝒰.I₀, Projective (f ∣_ ((𝒰.f i).opensRange))) :
    LocallyProjective f := sorry

end AlgebraicGeometry
