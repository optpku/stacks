/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Coherent.Support.Serre
public import ReasLib.AlgebraicGeometry.Scheme.Module.ClosedImmersion

/-!
# Coherent pushforward with set-theoretic support

This file regards coherent pushforward along a closed immersion as an exact functor into the
subcategory of coherent modules set-theoretically supported on the image.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules.ClosedImmersion

variable {X Z : Scheme.{u}}

/-- A coherent module annihilated by the ideal of a closed immersion is set-theoretically
supported on the image of that immersion. -/
theorem annihilated_le_supportedOn (i : Z ⟶ X) [IsClosedImmersion i] :
    coherentAnnihilated i ≤ RingedSpace.Coh.supportedOn (Set.range i.base) := sorry

/-- Coherent pushforward along a closed immersion, regarded as a functor into coherent modules
set-theoretically supported on the image. -/
noncomputable def toSupported [IsLocallyNoetherian X] [IsLocallyNoetherian Z]
    (i : Z ⟶ X) [IsClosedImmersion i] :
    RingedSpace.Coh Z.toRingedSpace ⥤
      RingedSpace.CohSupportedOn X.toRingedSpace (Set.range i.base) :=
  coherentPushforward i ⋙ ObjectProperty.ιOfLE (annihilated_le_supportedOn i)

/-- The underlying module of `toSupported i` is ordinary module pushforward along `i`. -/
theorem toSupported_obj [IsLocallyNoetherian X] [IsLocallyNoetherian Z]
    (i : Z ⟶ X) [IsClosedImmersion i] (F : RingedSpace.Coh Z.toRingedSpace) :
    ((toSupported i).obj F).obj.obj = (Scheme.Modules.pushforward i).obj F.obj := sorry

/-- Coherent pushforward into the supported subcategory is exact. -/
theorem toSupported_exact [IsLocallyNoetherian X] [IsLocallyNoetherian Z]
    (i : Z ⟶ X) [IsClosedImmersion i] :
    exactFunctor (RingedSpace.Coh Z.toRingedSpace)
      (RingedSpace.CohSupportedOn X.toRingedSpace (Set.range i.base))
      (toSupported i) := sorry

/-- Coherent pushforward into the supported subcategory, bundled as an exact functor. -/
noncomputable def toSupportedExact [IsLocallyNoetherian X] [IsLocallyNoetherian Z]
    (i : Z ⟶ X) [IsClosedImmersion i] :
    RingedSpace.Coh Z.toRingedSpace ⥤ₑ
      RingedSpace.CohSupportedOn X.toRingedSpace (Set.range i.base) :=
  ⟨toSupported i, toSupported_exact i⟩

/-- The object map of `toSupportedExact i` agrees with `toSupported i`. -/
theorem toSupportedExact_obj [IsLocallyNoetherian X] [IsLocallyNoetherian Z]
    (i : Z ⟶ X) [IsClosedImmersion i] (F : RingedSpace.Coh Z.toRingedSpace) :
    (toSupportedExact i).obj.obj F = (toSupported i).obj F := sorry

end AlgebraicGeometry.Scheme.Modules.ClosedImmersion
