module

public import ReasLib.AlgebraicGeometry.ProjectiveSpace.Relative
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.ClosedImmersion.Scheme
public import Mathlib.AlgebraicGeometry.Modules.Tilde

/-!
# Projective scheme morphisms

This file defines presentations of projective, H-projective, and locally projective scheme
morphisms using projective-bundle and relative-projective-space data.
-/

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry

section

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- A presentation of `f` as a closed immersion into a chosen projective bundle over its target. -/
structure ProjectivePresentation
    {P : Scheme.{u}} (f : X ⟶ S) (π : P ⟶ S) (i : X ⟶ P) : Prop where
  /-- The comparison morphism is a closed immersion. -/
  isClosedImmersion : IsClosedImmersion i
  /-- The comparison morphism lies over `f`. -/
  comp_eq : i ≫ π = f

namespace ProjectivePresentation

variable {P : Scheme.{u}} {π : P ⟶ S} {i : X ⟶ P}

/-- A closed immersion over the base morphism determines a projective presentation. -/
def ofClosedImmersion
    (h_i : IsClosedImmersion i) (h_comp : i ≫ π = f) :
    ProjectivePresentation f π i :=
  ⟨h_i, h_comp⟩

/-- The comparison morphism of a projective presentation lies over its base morphism. -/
@[reassoc (attr := simp)]
theorem w
    (h : ProjectivePresentation f π i) :
    i ≫ π = f := sorry

/-- The closed-immersion component of a projective presentation. -/
theorem closedImmersion
    (h : ProjectivePresentation f π i) :
    IsClosedImmersion i := sorry

end ProjectivePresentation

/-- A projective presentation consists exactly of a closed immersion whose composite is the
base morphism. -/
theorem projectivePresentation_iff
    {P : Scheme.{u}} {π : P ⟶ S} {i : X ⟶ P} :
    ProjectivePresentation f π i ↔ IsClosedImmersion i ∧ i ≫ π = f := sorry

/-- A scheme morphism is projective when it admits a closed-immersion presentation in a projective
bundle associated to a finite-type quasi-coherent module. -/
@[stacks 01W8]
class Projective (f : X ⟶ S) : Prop where
  /-- A finite-type quasi-coherent projective-bundle presentation of `f`. -/
  exists_presentation :
    ∃ (P : Scheme.{u}) (π : P ⟶ S) (ℰ : S.Modules),
      ℰ.IsFiniteType ∧ ℰ.IsQuasicoherent ∧
        ∃ _ : Scheme.ProjectiveBundle.Representation π ℰ, ∃ i : X ⟶ P,
          ProjectivePresentation f π i

/-- A scheme morphism is H-projective when it admits a closed-immersion presentation in a relative
projective space. -/
@[stacks 01W8]
class HProjective (f : X ⟶ S) : Prop where
  /-- A relative-projective-space presentation of `f`. -/
  exists_presentation :
    ∃ (n : ℕ) (P : ProjectiveSpaceOver S n) (i : X ⟶ P.scheme),
      ProjectivePresentation f P.hom i

/-- A scheme morphism is locally projective when it is projective after restricting to the members
of some open cover of its target. -/
@[stacks 01W8]
class LocallyProjective (f : X ⟶ S) : Prop where
  /-- A target open cover on whose members the restricted morphism is projective. -/
  exists_cover :
    ∃ 𝒰 : Scheme.OpenCover.{u} S, ∀ i : 𝒰.I₀,
      Projective (f ∣_ ((𝒰.f i).opensRange))

/-- The finite-type quasi-coherent projective-bundle presentation carried by a projective
morphism. -/
theorem Projective.presentation
    (h : Projective f) :
    ∃ (P : Scheme.{u}) (π : P ⟶ S) (ℰ : S.Modules),
      ℰ.IsFiniteType ∧ ℰ.IsQuasicoherent ∧
        ∃ _ : Scheme.ProjectiveBundle.Representation π ℰ, ∃ i : X ⟶ P,
          ProjectivePresentation f π i := sorry

/-- Projectivity is equivalent to the existence of a finite-type quasi-coherent projective-bundle
presentation. -/
theorem projective_iff :
    Projective f ↔
      ∃ (P : Scheme.{u}) (π : P ⟶ S) (ℰ : S.Modules),
        ℰ.IsFiniteType ∧ ℰ.IsQuasicoherent ∧
          ∃ _ : Scheme.ProjectiveBundle.Representation π ℰ, ∃ i : X ⟶ P,
            ProjectivePresentation f π i := sorry

/-- The relative-projective-space presentation carried by an H-projective morphism. -/
theorem HProjective.presentation
    (h : HProjective f) :
    ∃ (n : ℕ) (P : ProjectiveSpaceOver S n) (i : X ⟶ P.scheme),
      ProjectivePresentation f P.hom i := sorry

/-- H-projectivity is equivalent to the existence of a closed-immersion presentation in a relative
projective space. -/
theorem hProjective_iff :
    HProjective f ↔
      ∃ (n : ℕ) (P : ProjectiveSpaceOver S n) (i : X ⟶ P.scheme),
        ProjectivePresentation f P.hom i := sorry

/-- The target open cover carried by a locally projective morphism. -/
theorem LocallyProjective.openCover
    (h : LocallyProjective f) :
    ∃ 𝒰 : Scheme.OpenCover.{u} S, ∀ i : 𝒰.I₀,
      Projective (f ∣_ ((𝒰.f i).opensRange)) := sorry

/-- Local projectivity is equivalent to projectivity after restricting to the members of one
target open cover. -/
theorem locallyProjective_iff :
    LocallyProjective f ↔
      ∃ 𝒰 : Scheme.OpenCover.{u} S, ∀ i : 𝒰.I₀,
        Projective (f ∣_ ((𝒰.f i).opensRange)) := sorry

/-- Every H-projective morphism is projective. -/
theorem HProjective.toProjective
    (h : HProjective f) :
    Projective f := sorry

/-- H-projectivity supplies a projective morphism structure. -/
instance instProjectiveOfHProjective [HProjective f] :
    Projective f := sorry

/-- Every projective morphism is locally projective. -/
theorem Projective.toLocallyProjective
    (h : Projective f) :
    LocallyProjective f := sorry

/-- Projectivity supplies a locally projective morphism structure. -/
instance instLocallyProjectiveOfProjective [Projective f] :
    LocallyProjective f := sorry

end

end AlgebraicGeometry
