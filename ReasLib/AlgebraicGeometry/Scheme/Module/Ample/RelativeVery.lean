/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Ample.Relative
public import ReasLib.AlgebraicGeometry.Scheme.ProjectiveBundle.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Relative very ampleness of scheme modules

This module defines projective-bundle presentations of relatively very ample
modules and their basic consequences.
-/

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.MonoidalCategory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry

section

variable {X S P : Scheme.{u}} {f : X ⟶ S} {L : X.Modules}
variable {ℰ : S.Modules}

/-- A presentation of a module as the pullback of the tautological module along an immersion into
a projective bundle. -/
@[stacks 01VM "relative very ampleness presentation"]
structure RelativelyVeryAmplePresentation
    (f : X ⟶ S) (L : X.Modules)
    (π : P ⟶ S) (ℰ : S.Modules)
    (hπ : Scheme.ProjectiveBundle.Representation π ℰ)
    (i : X ⟶ P) : Prop where
  /-- The comparison map into the projective bundle is an immersion. -/
  isImmersion : IsImmersion i
  /-- The immersion lies over the base morphism. -/
  comp_eq : i ≫ π = f
  /-- Pulling back the tautological module recovers the prescribed module. -/
  pullbackIso :
    Nonempty
      (L ≅
        (Scheme.Modules.pullback i).obj
          (Scheme.ProjectiveBundle.tautologicalSheaf π hπ))

/-- Build a relative-very-ample presentation from a specified lift into the projective bundle,
an immersion proof, and a tautological pullback isomorphism. -/
def RelativelyVeryAmplePresentation.ofLift
    (hπ : Scheme.ProjectiveBundle.Representation π ℰ)
    (j : Scheme.ProjectiveBundle.Lift π f)
    (hj : IsImmersion j.hom)
    (pullbackIso :
      Nonempty
        (L ≅
          (Scheme.Modules.pullback j.hom).obj
            (Scheme.ProjectiveBundle.tautologicalSheaf π hπ))) :
    RelativelyVeryAmplePresentation f L π ℰ hπ j.hom :=
  ⟨hj, j.fac, pullbackIso⟩

/-- A relative-very-ample presentation is precisely an immersion over the base whose pullback of
the tautological module is the prescribed module. -/
theorem RelativelyVeryAmplePresentation.iff
    (hπ : Scheme.ProjectiveBundle.Representation π ℰ) :
    RelativelyVeryAmplePresentation f L π ℰ hπ i ↔
      IsImmersion i ∧
        i ≫ π = f ∧
          Nonempty
            (L ≅
              (Scheme.Modules.pullback i).obj
                (Scheme.ProjectiveBundle.tautologicalSheaf π hπ)) := sorry

/-- A module is relatively very ample when it admits a quasi-coherent projective-bundle
presentation as the pullback of the tautological module. -/
@[stacks 01VM "relatively very ample module"]
class RelativelyVeryAmple (f : X ⟶ S) (L : X.Modules) : Prop where
  /-- The module is invertible on the source. -/
  invertible : Scheme.Modules.Invertible L
  /-- A projective-bundle presentation exists. -/
  exists_presentation :
    ∃ (P : Scheme.{u}) (π : P ⟶ S) (ℰ : S.Modules),
      ℰ.IsQuasicoherent ∧
        ∃ (hπ : Scheme.ProjectiveBundle.Representation π ℰ) (i : X ⟶ P),
          RelativelyVeryAmplePresentation f L π ℰ hπ i

/-- Relative very ampleness is equivalent to invertibility together with an immersion over the
base into a projective bundle of a quasi-coherent module, identifying the given module with the
pullback of the tautological module. -/
theorem RelativelyVeryAmple.iff :
    RelativelyVeryAmple f L ↔
      Scheme.Modules.Invertible L ∧
        ∃ (P : Scheme.{u}) (π : P ⟶ S) (ℰ : S.Modules),
          ℰ.IsQuasicoherent ∧
            ∃ (hπ : Scheme.ProjectiveBundle.Representation π ℰ) (i : X ⟶ P),
              IsImmersion i ∧
                i ≫ π = f ∧
                  Nonempty
                    (L ≅
                      (Scheme.Modules.pullback i).obj
                        (Scheme.ProjectiveBundle.tautologicalSheaf π hπ)) := sorry

namespace RelativelyVeryAmple

/-- Relative very ampleness of the restriction to the inverse image of a base open. -/
@[stacks 01VR "relative very ampleness on a base-open preimage"]
abbrev onBasePreimage (f : X ⟶ S) (L : X.Modules) (V : S.Opens) : Prop :=
  RelativelyVeryAmple (f ∣_ V) (restrictToBasePreimage f L V)

end RelativelyVeryAmple

/-- A relatively very ample module is invertible for the canonical tensor product. -/
theorem RelativelyVeryAmple.isInvertible
    (h : RelativelyVeryAmple f L) :
    Scheme.Modules.Invertible L := sorry

/-- Extract the quasi-coherent projective-bundle presentation carried by a relatively very ample
module. -/
theorem RelativelyVeryAmple.presentation
    (h : RelativelyVeryAmple f L) :
    ∃ (P : Scheme.{u}) (π : P ⟶ S) (ℰ : S.Modules),
      ℰ.IsQuasicoherent ∧
        ∃ (hπ : Scheme.ProjectiveBundle.Representation π ℰ) (i : X ⟶ P),
          RelativelyVeryAmplePresentation f L π ℰ hπ i := sorry

/-- A relatively very ample module has separated structure morphism. -/
theorem RelativelyVeryAmple.isSeparated
    (h : RelativelyVeryAmple f L) :
    IsSeparated f := sorry

/-- A relatively very ample module is relatively ample when the structure
morphism is quasi-compact. -/
@[stacks 01VN "relative very ampleness implies relative ampleness"]
theorem RelativelyVeryAmple.relativelyAmple_of_quasiCompact
    [QuasiCompact f]
    (h : RelativelyVeryAmple f L) :
    RelativelyAmple f L := sorry

/-- A relatively very ample module over a quasi-compact morphism is canonically
relatively ample. -/
instance instRelativelyAmpleOfRelativelyVeryAmple
    [QuasiCompact f]
    [h : RelativelyVeryAmple f L] :
    RelativelyAmple f L :=
  RelativelyVeryAmple.relativelyAmple_of_quasiCompact h

end

end AlgebraicGeometry
