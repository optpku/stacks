/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalDeformation.Stalk
public import ReasLib.AlgebraicGeometry.FormalDeformation.FlatAlgebra.Product
public import ReasLib.AlgebraicGeometry.FormalDeformation.FlatAlgebra.HenselCompletion

/-!
# Products of local comparisons of scheme deformations

Taking stalks at a family of points, henselizing the resulting local rings,
and completing them give based functors of deformation categories.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Functor IsLocalRing RingPairCat
open scoped BasedFunctor

universe u

noncomputable section

namespace FlatSchemeCat

variable (Λ k : Type u) [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable (X : Scheme.{u})
  (hX : X ⟶ Spec (CommRingCat.of (ArtinianLocalAlgCat.residue Λ k).carrier))
variable [AlgebraicGeometry.Flat hX]
variable {ι : Type u}

/-- The projection from scheme deformations to their Artinian local bases. -/
abbrev deformationForget : deformationCategory Λ k X hX ⥤ ArtinianLocalAlgCat Λ k :=
  Over.forget (Fiber.fiberInclusion.obj (residueObj Λ k X hX)) ⋙ forget Λ k

/-- The slice projection of `Def_X` evaluates an object `(A, Y) → (k, X)` to `A`. -/
theorem deformationForget_obj (ξ : deformationCategory Λ k X hX) :
    (deformationForget Λ k X hX).obj ξ = ξ.left.base :=
  rfl

/-- The slice projection of `Def_X` is cofibered in groupoids. -/
instance instInGroupoids_deformationForget :
    IsFibered.InGroupoids (deformationForget Λ k X hX).op :=
  sorry

/-- Stalk at each named point, as a based functor into the product of the local
deformation categories. -/
def stalkPiBasedFunctor (p : ι → X) :
    BasedCategory.ofFunctor (deformationForget Λ k X hX) ⥤ᵇ
      BasedCategory.ofFunctor
        (FlatAlgebraCat.deformationPiForget Λ k fun i ↦ structureStalk X hX (p i)) :=
  FlatAlgebraCat.pairing Λ k (fun i ↦ structureStalk X hX (p i))
    (deformationForget Λ k X hX) fun i ↦ stalkAlgebraBasedFunctor Λ k X hX (p i)

/-- The underlying functor of `stalkPiBasedFunctor` retains the Artinian base. -/
theorem stalkPiBasedFunctor_obj_base (p : ι → X) (ξ : deformationCategory Λ k X hX) :
    ((stalkPiBasedFunctor Λ k X hX p).toFunctor.obj ξ).1 =
      (deformationForget Λ k X hX).obj ξ :=
  sorry

/-- The `i`-th factor of `stalkPiBasedFunctor` is `stalkAlgebraBasedFunctor` at
`p i`. -/
theorem stalkPiBasedFunctor_eval (p : ι → X) (ξ : deformationCategory Λ k X hX) (i : ι) :
    (FlatAlgebraCat.evalBasedFunctor Λ k (fun j ↦ structureStalk X hX (p j)) i).toFunctor.obj
        ((stalkPiBasedFunctor Λ k X hX p).toFunctor.obj ξ) =
      (stalkAlgebraBasedFunctor Λ k X hX (p i)).toFunctor.obj ξ :=
  sorry

variable [henselianPairInclusion.IsRightAdjoint]

/-- Pair henselization of each local stalk, as a based functor of deformation
products. -/
def henselizationPiBasedFunctor [IsLocallyNoetherian X] (p : ι → X) :
    BasedCategory.ofFunctor
        (FlatAlgebraCat.deformationPiForget Λ k fun i ↦ structureStalk X hX (p i)) ⥤ᵇ
      BasedCategory.ofFunctor
        (FlatAlgebraCat.deformationPiForget Λ k fun i ↦ henselStalk X hX (p i)) :=
  FlatAlgebraCat.deformationPiMap Λ k (fun i ↦ structureStalk X hX (p i))
    (fun i ↦ henselStalk X hX (p i)) fun i ↦
      FlatAlgebraCat.henselizationLocalBasedFunctor Λ k (structureStalk X hX (p i))

/-- The underlying functor of `henselizationPiBasedFunctor` retains the Artinian
base. -/
theorem henselizationPiBasedFunctor_obj_base [IsLocallyNoetherian X] (p : ι → X)
    (x : FlatAlgebraCat.deformationPi Λ k fun i ↦ structureStalk X hX (p i)) :
    ((henselizationPiBasedFunctor Λ k X hX p).toFunctor.obj x).1 = x.1 :=
  sorry

/-- The `i`-th factor of `henselizationPiBasedFunctor` is pair henselization of
`structureStalk` along its maximal ideal. -/
theorem henselizationPiBasedFunctor_eval [IsLocallyNoetherian X] (p : ι → X)
    (x : FlatAlgebraCat.deformationPi Λ k fun i ↦ structureStalk X hX (p i)) (i : ι) :
    (FlatAlgebraCat.evalBasedFunctor Λ k (fun j ↦ henselStalk X hX (p j)) i).toFunctor.obj
        ((henselizationPiBasedFunctor Λ k X hX p).toFunctor.obj x) =
      (FlatAlgebraCat.henselizationLocalBasedFunctor Λ k (structureStalk X hX (p i))).toFunctor.obj
        (Fiber.fiberInclusion.obj (x.2 i)) :=
  sorry

/-- Adic completion of each henselian local stalk, as a based functor of
deformation products landing in `∏ Def_{O_{X, p i}^∧}`. -/
def completionPiBasedFunctor [IsLocallyNoetherian X] (p : ι → X) :
    BasedCategory.ofFunctor
        (FlatAlgebraCat.deformationPiForget Λ k fun i ↦ henselStalk X hX (p i)) ⥤ᵇ
      BasedCategory.ofFunctor
        (FlatAlgebraCat.deformationPiForget Λ k fun i ↦ completeStalk X hX (p i)) :=
  FlatAlgebraCat.deformationPiMap Λ k (fun i ↦ henselStalk X hX (p i))
    (fun i ↦ completeStalk X hX (p i)) fun i ↦
      FlatAlgebraCat.completionFromHenselLocalBasedFunctor Λ k (structureStalk X hX (p i))

/-- The underlying functor of `completionPiBasedFunctor` retains the Artinian base. -/
theorem completionPiBasedFunctor_obj_base [IsLocallyNoetherian X] (p : ι → X)
    (x : FlatAlgebraCat.deformationPi Λ k fun i ↦ henselStalk X hX (p i)) :
    ((completionPiBasedFunctor Λ k X hX p).toFunctor.obj x).1 = x.1 :=
  sorry

/-- The `i`-th factor of `completionPiBasedFunctor` is the henselization-to-completion
transport `completionFromHenselLocalBasedFunctor`. -/
theorem completionPiBasedFunctor_eval [IsLocallyNoetherian X] (p : ι → X)
    (x : FlatAlgebraCat.deformationPi Λ k fun i ↦ henselStalk X hX (p i)) (i : ι) :
    (FlatAlgebraCat.evalBasedFunctor Λ k (fun j ↦ completeStalk X hX (p j)) i).toFunctor.obj
        ((completionPiBasedFunctor Λ k X hX p).toFunctor.obj x) =
      (FlatAlgebraCat.completionFromHenselLocalBasedFunctor Λ k
          (structureStalk X hX (p i))).toFunctor.obj
        (Fiber.fiberInclusion.obj (x.2 i)) :=
  sorry

end FlatSchemeCat

end

