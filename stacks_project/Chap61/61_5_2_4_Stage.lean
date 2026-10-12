/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Algebra.Pi
public import Mathlib.AlgebraicGeometry.Scheme
public import stacks_project.Chap61.«61_5_2_1_Stage»

/-!
# Vanishing-pattern stage spectra

The finite-stage affine scheme `X_E` is the spectrum of the vanishing-pattern
stage algebra `Algebra.WLocalHull.stage A E`.
-/

@[expose] public section

open AlgebraicGeometry Algebra.WLocalHull

universe u

namespace Algebra.WLocalHull

variable (A : Type u) [CommRing A]

/-- The finite-stage affine scheme `X_E = Spec(A_E)`. -/
noncomputable def spectrum (E : Finset A) : Scheme.{u} :=
  Spec (.of (stage A E))

/-- The product of the standard affine charts `(A ⧸ I)_f` of the strata of `E`. -/
abbrev closedStage (E : Finset A) : Type u :=
  ∀ p : Pattern A E, stratumSections A p.elem p.span

/-- The canonical surjection `A_Z^~ → (A ⧸ I)_f` of lemma-localization. -/
noncomputable def toClosedStage {E : Finset A} (p : Pattern A E) :
    specializingLocalization A p.elem p.span →+* stratumSections A p.elem p.span :=
  IsLocalization.lift (M := specializingSubmonoid A p.elem p.span)
    (g := toStratumSections A p.elem p.span) fun y ↦
      (IsUnit.mem_submonoid_iff _).mp
        (Submonoid.mem_comap.mp
          (y.property : (y : A) ∈ (IsUnit.submonoid (stratumSections A p.elem p.span)).comap
            (toStratumSections A p.elem p.span)))

/-- The product of the canonical surjections `A_Z^~ → (A ⧸ I)_f`. -/
noncomputable def closedStageMap (E : Finset A) : stage A E →+* closedStage A E :=
  RingHom.pi fun p ↦ (toClosedStage A p).comp (stage.eval A p)

/-- The closed subscheme morphism `Z_E ⟶ X_E` induced by `closedStageMap`. -/
noncomputable def closedHom (E : Finset A) :
    Spec (.of (closedStage A E)) ⟶ spectrum A E :=
  Spec.map (CommRingCat.ofHom (closedStageMap A E))

end Algebra.WLocalHull
