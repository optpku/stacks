/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Geometry.RingedSpace.Basic
public import ReasLib.RingTheory.Sequence.QuasiRegular.Regularity

/-!
# Regular finite families of sections on ringed spaces

This module expresses regularity conditions for a finite family of sections by applying the
corresponding commutative-algebra condition to its germs at every point.
-/

@[expose] public section

universe u

open Opposite TopologicalSpace

namespace AlgebraicGeometry.RingedSpace.SectionSequence

variable {X : RingedSpace.{u}} {U : Opens X} {r : ℕ}

/-- The ordered family of germs at a point of a finite family of sections on an open. -/
noncomputable def germFamily (f : Fin r → X.presheaf.obj (op U)) (x : X) (hx : x ∈ U) :
    Fin r → X.presheaf.stalk x :=
  fun i ↦ X.presheaf.germ U x hx (f i)

/-- A finite family of sections is regular when its germ family is weakly regular at every point
of its open domain. -/
def IsRegular (f : Fin r → X.presheaf.obj (op U)) : Prop :=
  ∀ (x : X) (hx : x ∈ U),
    RingTheory.Sequence.IsWeaklyRegular (X.presheaf.stalk x)
      (List.ofFn (germFamily f x hx))

/-- A finite family of sections is Koszul-regular when its germ family is Koszul-regular at every
point of its open domain. -/
def IsKoszulRegular (f : Fin r → X.presheaf.obj (op U)) : Prop :=
  ∀ (x : X) (hx : x ∈ U),
    RingTheory.Sequence.IsKoszulRegularSequence (germFamily f x hx)

/-- A finite family of sections is `H₁`-regular when its germ family is `H₁`-regular at every
point of its open domain. -/
def IsH1Regular (f : Fin r → X.presheaf.obj (op U)) : Prop :=
  ∀ (x : X) (hx : x ∈ U),
    RingTheory.Sequence.IsH1RegularSequence (germFamily f x hx)

/-- A finite family of sections is quasi-regular when its germ family, in its given order, is
quasi-regular at every point of its open domain. -/
def IsQuasiRegular (f : Fin r → X.presheaf.obj (op U)) : Prop :=
  ∀ (x : X) (hx : x ∈ U),
    RingTheory.Sequence.IsQuasiRegularSequence (List.ofFn (germFamily f x hx))

namespace IsRegular

/-- Every regular finite family of sections is Koszul-regular. -/
theorem isKoszulRegular {f : Fin r → X.presheaf.obj (op U)}
    (hreg : IsRegular f) : IsKoszulRegular f := by
  intro x hx
  exact RingTheory.Sequence.isKoszulRegularSequence_of_isWeaklyRegular (hreg x hx)

end IsRegular

namespace IsKoszulRegular

/-- Every Koszul-regular finite family of sections is `H₁`-regular. -/
theorem isH1Regular {f : Fin r → X.presheaf.obj (op U)}
    (hKoszul : IsKoszulRegular f) : IsH1Regular f := by
  intro x hx
  exact RingTheory.Sequence.isH1RegularSequence_of_isKoszulRegularSequence (hKoszul x hx)

end IsKoszulRegular

namespace IsH1Regular

/-- Every `H₁`-regular finite family of sections is quasi-regular. -/
theorem isQuasiRegular {f : Fin r → X.presheaf.obj (op U)}
    (hH1 : IsH1Regular f) : IsQuasiRegular f := by
  intro x hx
  exact RingTheory.Sequence.IsH1RegularOn.isQuasiRegular (hH1 x hx)

end IsH1Regular

end AlgebraicGeometry.RingedSpace.SectionSequence
