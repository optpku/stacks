/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.SheafAdjunction
public import ReasLib.CategoryTheory.Sites.LocallyBijective.Inverse
public import Mathlib.CategoryTheory.Limits.Preserves.Limits

/-!
# Finite-limit descent for the constructed geometric inverse image

The limit comparison is the usual forward map of the actual chart-Kan and
sheafification inverse image. Its reverse glues local preimages on its specified
image sieve. Finite-limit preservation is packaged from those two maps.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.EtaleTopos

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
variable {I : Type} [SmallCategory I]
variable (K : I ⥤ Sheaf (smallEtaleTopology Y) (Type u))

/-- Finite compatible families have local lifts through the actual geometric
limit comparison. The cover is its specified image sieve. -/
instance limitComparisonLocallySurjective [FinCategory I] :
    Sheaf.IsLocallySurjective (limit.post K (inverseImage f)) := sorry

/-- Two local lifts of a finite compatible family coincide locally. -/
instance limitComparisonLocallyInjective [FinCategory I] :
    Sheaf.IsLocallyInjective (limit.post K (inverseImage f)) := sorry

/-- The actual finite-limit comparison with its reverse by image-sieve descent. -/
def finiteLimitIso [FinCategory I] :
    (inverseImage f).obj (limit K) ≅ limit (K ⋙ inverseImage f) :=
  Sheaf.isoOfLocallyBijective (limit.post K (inverseImage f))

@[simp]
theorem finiteLimitIso_hom [FinCategory I] :
    (finiteLimitIso f K).hom = limit.post K (inverseImage f) := rfl

/-- The reverse section is precisely the glued family of local preimages. -/
@[simp]
theorem finiteLimitIso_inv_app [FinCategory I] (U : (smallEtaleSite X)ᵒᵖ)
    (s : (limit (K ⋙ inverseImage f)).obj.obj U) :
    (finiteLimitIso f K).inv.hom.app U s =
      Sheaf.localInverseSection (limit.post K (inverseImage f)) U s := rfl

/-- A cone is lifted by the genuine target limit lift followed by local descent. -/
def finiteLimitLift [FinCategory I] (c : Cone (K ⋙ inverseImage f)) :
    c.pt ⟶ (inverseImage f).obj (limit K) :=
  limit.lift _ c ≫ (finiteLimitIso f K).inv

/-- The mapped chosen limit has the specified lift; only its laws are proof debt. -/
def finiteLimitIsLimit [FinCategory I] :
    IsLimit ((inverseImage f).mapCone (limit.cone K)) where
  lift := finiteLimitLift f K
  fac := sorry
  uniq := sorry

/-- The constructed geometric inverse image preserves finite limits using the
explicit mapped-cone limit data. -/
instance leftExact : PreservesFiniteLimits (inverseImage f) where
  preservesFiniteLimits I _ _ :=
    { preservesLimit := fun {K} ↦
        preservesLimit_of_preserves_limit_cone (limit.isLimit K)
          (finiteLimitIsLimit f K) }

end AlgebraicGeometry.AlgebraicSpace.EtaleTopos
