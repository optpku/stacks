/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import ReasLib.AlgebraicGeometry.Scheme.Frobenius.Absolute
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Characteristic

/-!
# Relative Frobenius of scheme morphisms

This leaf packages the Frobenius twist of a scheme morphism and the canonical
relative Frobenius map into that twist.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

universe u

noncomputable section

namespace AlgebraicGeometry.Scheme.Hom

section

variable {p : ℕ} [Fact p.Prime]
variable {X S : Scheme.{u}} (f : X ⟶ S)
variable [Scheme.IsCharP S p]

/-- The Frobenius twist of `f : X ⟶ S`, formed by pulling `f` back along the absolute Frobenius
of `S`. -/
@[stacks 0CC9]
abbrev relativeFrobeniusTarget : Scheme.{u} :=
  pullback f (Scheme.absoluteFrobenius p S)

/-- The Frobenius twist of `f`, viewed as a scheme over `S` by its second pullback projection. -/
def relativeFrobeniusTargetOver : Over S :=
  Over.mk (pullback.snd f (Scheme.absoluteFrobenius p S))

/-- The square defining the Frobenius twist of `f` is cartesian. -/
theorem relativeFrobeniusTarget_isPullback :
    IsPullback (pullback.fst f (Scheme.absoluteFrobenius p S))
      (relativeFrobeniusTargetOver (p := p) f).hom f
        (Scheme.absoluteFrobenius p S) := sorry

/-- The relative Frobenius morphism from `X` to the Frobenius twist of `f`. -/
@[stacks 0CC9]
def relativeFrobenius :
    X ⟶ relativeFrobeniusTarget (p := p) f :=
  -- Local instance justification (search instability): `f` canonically induces the characteristic on `X`, but global instance search cannot infer `f`.
  letI : Scheme.IsCharP X p := isCharP_of_target (p := p) f
  pullback.lift (Scheme.absoluteFrobenius p X) f (absoluteFrobenius_commSq f).w

/-- The first projection from the relative Frobenius is the absolute Frobenius of the source. -/
@[stacks 0CC9]
theorem relativeFrobenius_fst :
    -- Local instance justification (search instability): `f` canonically induces the characteristic on `X`, but global instance search cannot infer `f`.
    letI : Scheme.IsCharP X p := isCharP_of_target (p := p) f
    relativeFrobenius (p := p) f ≫ pullback.fst f (Scheme.absoluteFrobenius p S) =
      Scheme.absoluteFrobenius p X := sorry

/-- The second projection from the relative Frobenius is the original structure morphism. -/
@[stacks 0CC9]
theorem relativeFrobenius_snd :
    relativeFrobenius (p := p) f ≫ pullback.snd f (Scheme.absoluteFrobenius p S) = f := sorry

/-- The relative Frobenius, bundled as a morphism of schemes over `S`. -/
def relativeFrobeniusOver :
    Over.mk f ⟶ relativeFrobeniusTargetOver (p := p) f :=
  Over.homMk (relativeFrobenius (p := p) f) (relativeFrobenius_snd (p := p) f)

/-- A morphism to the Frobenius twist with the same two projections as the relative
Frobenius is the relative Frobenius. -/
theorem relativeFrobenius_unique
    (g : X ⟶ relativeFrobeniusTarget (p := p) f)
    (hfst :
      -- Local instance justification (search instability): `f` canonically induces the characteristic on `X`, but global instance search cannot infer `f`.
      letI : Scheme.IsCharP X p := isCharP_of_target (p := p) f
      g ≫ pullback.fst f (Scheme.absoluteFrobenius p S) =
        Scheme.absoluteFrobenius p X)
    (hsnd : g ≫ pullback.snd f (Scheme.absoluteFrobenius p S) = f) :
    g = relativeFrobenius (p := p) f := sorry

end

end AlgebraicGeometry.Scheme.Hom
