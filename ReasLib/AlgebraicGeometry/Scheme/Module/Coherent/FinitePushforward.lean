/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.AssociatedCycle.Pushforward
public import ReasLib.AlgebraicGeometry.Scheme.Module.Coherent.Finite
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Coherent.SupportDimension.Serre
public import ReasLib.CategoryTheory.ObjectProperty.FullSubcategory.Restriction
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor

/-!
# Finite pushforward of coherent modules

This file defines finite pushforward on coherent modules and on the relative
support-dimension filtration.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules.FinitePushforward

section Coherent

variable {S : Scheme.{u}} {X Y : Over S} (π : X ⟶ Y)
  [IsLocallyNoetherian S] [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
  [IsFinite π.left]

/-- Pushforward along a finite morphism, restricted to coherent sheaves. -/
noncomputable def coh :
    RingedSpace.Coh X.left.toRingedSpace ⥤ RingedSpace.Coh Y.left.toRingedSpace :=
  ObjectProperty.FullSubcategory.restrict (Scheme.Modules.pushforward π.left)
    (fun F hF ↦ @pushforward_obj_isCoherent_of_isFinite X.left Y.left π.left
      inferInstance (LocallyOfFiniteType.isLocallyNoetherian Y.hom) F hF)

/-- The underlying module of finite coherent pushforward is ordinary module pushforward. -/
theorem coh_obj (F : RingedSpace.Coh X.left.toRingedSpace) :
    ((coh π).obj F).obj = (Scheme.Modules.pushforward π.left).obj F.obj := sorry

/-- The underlying morphism of finite coherent pushforward is ordinary module pushforward. -/
theorem coh_map {F G : RingedSpace.Coh X.left.toRingedSpace} (f : F ⟶ G) :
    ((coh π).map f).hom = (Scheme.Modules.pushforward π.left).map f.hom := sorry

/-- Finite pushforward on coherent sheaves is exact. -/
theorem coh_exact :
    exactFunctor (RingedSpace.Coh X.left.toRingedSpace)
      (RingedSpace.Coh Y.left.toRingedSpace) (coh π) := sorry

/-- Finite pushforward on coherent sheaves, bundled as an exact functor. -/
noncomputable def cohExact :
    RingedSpace.Coh X.left.toRingedSpace ⥤ₑ RingedSpace.Coh Y.left.toRingedSpace :=
  ⟨coh π, coh_exact π⟩

end Coherent

section Filtered

variable {S : Scheme.{u}} {X Y : Over S} (π : X ⟶ Y)
  [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom] [IsFinite π.left]
variable (δ : S → ℤ) [UniversallyCatenary S] [IsDimensionFunction δ]

/-- Finite pushforward preserves the relative support-dimension bound. -/
theorem supportDimensionLE (k : ℤ) (F : RingedSpace.Coh X.left.toRingedSpace)
    (hF : RingedSpace.Coh.supportDimensionLE
      (X.hom.relativeDimensionFunction δ) k F) :
    RingedSpace.Coh.supportDimensionLE (Y.hom.relativeDimensionFunction δ) k
      ((coh π).obj F) := sorry

/-- Finite pushforward restricted to coherent sheaves of relative support dimension at most
`k`. -/
noncomputable def cohLE (k : ℤ) :
    RingedSpace.CohLE X.left.toRingedSpace (X.hom.relativeDimensionFunction δ) k ⥤
      RingedSpace.CohLE Y.left.toRingedSpace (Y.hom.relativeDimensionFunction δ) k :=
  ObjectProperty.FullSubcategory.restrict (coh π)
    (fun F hF ↦ supportDimensionLE π δ k F hF)

/-- The underlying coherent sheaf of filtered finite pushforward is `coh`. -/
theorem cohLE_obj (k : ℤ)
    (F : RingedSpace.CohLE X.left.toRingedSpace
      (X.hom.relativeDimensionFunction δ) k) :
    ((cohLE π δ k).obj F).obj = (coh π).obj F.obj := sorry

/-- Finite pushforward on support-dimension-filtered coherent sheaves is exact. -/
theorem cohLE_exact (k : ℤ) :
    exactFunctor
      (RingedSpace.CohLE X.left.toRingedSpace (X.hom.relativeDimensionFunction δ) k)
      (RingedSpace.CohLE Y.left.toRingedSpace (Y.hom.relativeDimensionFunction δ) k)
      (cohLE π δ k) := sorry

/-- Filtered finite pushforward, bundled as an exact functor. -/
noncomputable def cohLEExact (k : ℤ) :
    RingedSpace.CohLE X.left.toRingedSpace (X.hom.relativeDimensionFunction δ) k ⥤ₑ
      RingedSpace.CohLE Y.left.toRingedSpace (Y.hom.relativeDimensionFunction δ) k :=
  ⟨cohLE π δ k, cohLE_exact π δ k⟩

end Filtered

end AlgebraicGeometry.Scheme.Modules.FinitePushforward
