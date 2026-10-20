module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Pullback.Coherent
public import ReasLib.AlgebraicGeometry.Scheme.ProjectiveLineFamily.Section

/-!
# Module restrictions on projective-line families

This file defines restriction of a module on `X ×ₛ ℙ¹ₛ` to its canonical zero and infinity
sections.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.ProjectiveLineFamily

/-- The pullback of a module on `X ×ₛ ℙ¹ₛ` to the zero section. -/
noncomputable def zeroRestriction {S : Scheme.{u}} (X : Over S)
    (F : (space X).Modules) : X.left.Modules :=
  (Scheme.Modules.pullback (zeroSection X)).obj F

/-- The zero restriction is the canonical module pullback along `i₀`. -/
theorem zeroRestriction_def {S : Scheme.{u}} (X : Over S) (F : (space X).Modules) :
    zeroRestriction X F = (Scheme.Modules.pullback (zeroSection X)).obj F := sorry

/-- The pullback of a module on `X ×ₛ ℙ¹ₛ` to the infinity section. -/
noncomputable def infinityRestriction {S : Scheme.{u}} (X : Over S)
    (F : (space X).Modules) : X.left.Modules :=
  (Scheme.Modules.pullback (infinitySection X)).obj F

/-- The infinity restriction is the canonical module pullback along `i∞`. -/
theorem infinityRestriction_def {S : Scheme.{u}} (X : Over S)
    (F : (space X).Modules) :
    infinityRestriction X F = (Scheme.Modules.pullback (infinitySection X)).obj F := sorry

end AlgebraicGeometry.ProjectiveLineFamily
