/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.K0.Comparison
public import ReasLib.AlgebraicGeometry.Scheme.Module.ClosedImmersion.CoherentSupport
public import ReasLib.CategoryTheory.Abelian.GrothendieckGroup.Functor

/-!
# Grothendieck groups of coherent sheaves with support

This file defines the Grothendieck group of coherent module sheaves supported on a prescribed
subset and the homomorphism induced by coherent pushforward along a closed immersion.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

/-- The Grothendieck group of coherent module sheaves on `X` supported on `T`. -/
abbrev K0'WithSupport (X : Scheme.{u}) [IsLocallyNoetherian X] (T : Set X) : Type (u + 1) :=
  AbelianK0 (RingedSpace.CohSupportedOn X.toRingedSpace T)

namespace K0'WithSupport

/-- The class of a supported coherent module sheaf in `K0'WithSupport X T`. -/
def of (X : Scheme.{u}) [IsLocallyNoetherian X] (T : Set X)
    (F : RingedSpace.CohSupportedOn X.toRingedSpace T) : K0'WithSupport X T :=
  AbelianK0.of F

/-- The supported coherent class constructor is the canonical `AbelianK0` generator. -/
theorem of_def (X : Scheme.{u}) [IsLocallyNoetherian X] (T : Set X)
    (F : RingedSpace.CohSupportedOn X.toRingedSpace T) :
    of X T F = AbelianK0.of F := sorry

variable {X Z : Scheme.{u}}

/-- The homomorphism on coherent Grothendieck groups induced by pushforward along a closed
immersion, with codomain restricted by set-theoretic support. -/
noncomputable def closedPushforward [IsLocallyNoetherian X]
    (i : Z ⟶ X) [IsClosedImmersion i] :
    @K0' Z (LocallyOfFiniteType.isLocallyNoetherian i) →+
      K0'WithSupport X (Set.range i.base) :=
  (AbelianK0.map
      (@Modules.ClosedImmersion.toSupportedExact X Z inferInstance
        (LocallyOfFiniteType.isLocallyNoetherian i) i inferInstance)).comp
    (@K0'.toAbelianK0 Z (LocallyOfFiniteType.isLocallyNoetherian i))

/-- Closed pushforward sends the class of a coherent module to the class of its supported
pushforward. -/
theorem closedPushforward_of [IsLocallyNoetherian X]
    (i : Z ⟶ X) [IsClosedImmersion i] (F : RingedSpace.Coh Z.toRingedSpace) :
    closedPushforward i
        (ObjectProperty.GrothendieckGroup.of
          (SheafOfModules.isCoherent Z.toRingedSpace.ringCatSheaf) F) =
      of X (Set.range i.base)
        ((@Modules.ClosedImmersion.toSupported X Z inferInstance
          (LocallyOfFiniteType.isLocallyNoetherian i) i inferInstance).obj F) := sorry

/-- Coherent pushforward along a closed immersion into a locally Noetherian scheme induces a
bijection onto the Grothendieck group of coherent modules set-theoretically supported on its
image. -/
theorem closedPushforward_bijective {X Z : Scheme.{u}} [IsLocallyNoetherian X]
    (i : Z ⟶ X) [IsClosedImmersion i] :
    Function.Bijective (closedPushforward i) := sorry

end K0'WithSupport

end AlgebraicGeometry.Scheme
