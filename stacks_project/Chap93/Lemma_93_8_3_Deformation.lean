/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.DualNumber
public import Mathlib.CategoryTheory.FiberedCategory.Cocartesian
public import stacks_project.Chap90.Definition_90_12_1_DualNumber
public import stacks_project.Chap93.Example_93_8_1_Rings_Category

/-!
# Trivial dual-number lift of a ring deformation

The residue-fibre slice projection of `Def_P` and the trivial `k[ε]`-algebra
`P[ε] = DualNumber P` of Example 93.8.1.
-/

@[expose] public section

open CategoryTheory Functor
open ArtinianLocalAlgCat
open TrivSqZeroExt

noncomputable section

universe u

namespace FlatAlgebraCat

variable (Λ k : Type u) [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

/-- The slice projection `Def_P ⥤ C_Λ` of Example 93.8.1. -/
abbrev deformationForget (P : Type u) [CommRing P] [Algebra k P] :
    deformationCategory Λ k P ⥤ ArtinianLocalAlgCat Λ k :=
  Over.forget (Fiber.fiberInclusion.obj (residueObj Λ k P)) ⋙ forget

/-- `deformationForget` is the composite of the Over-forgetful functor with `forget`. -/
theorem deformationForget_eq (P : Type u) [CommRing P] [Algebra k P] :
    deformationForget Λ k P =
      Over.forget (Fiber.fiberInclusion.obj (residueObj Λ k P)) ⋙ forget := sorry

/-- `deformationForget` sends a deformation `(A, Q)` to the Artinian local algebra `A`. -/
theorem deformationForget_obj (P : Type u) [CommRing P] [Algebra k P]
    (ξ : deformationCategory Λ k P) :
    (deformationForget Λ k P).obj ξ = ξ.left.base := sorry

/-- The slice projection of `Def_P` is a predeformation category. -/
instance instIsPredeformationCategory_deformationForget
    (P : Type u) [CommRing P] [Algebra k P] :
    IsPredeformationCategory (deformationForget Λ k P) := sorry

/-- Predeformation categories are cofibered in groupoids. -/
instance instIsFiberedInGroupoids_deformationForget_op
    (P : Type u) [CommRing P] [Algebra k P] :
    IsFibered.InGroupoids (deformationForget Λ k P).op :=
  IsPredeformationCategory.isCofiberedInGroupoids

/-- The inclusion `k ⟶ k[ε]` in `ArtinianLocalAlgCat`, as a morphism of the 90.12.1 dual-number
object over the residue object of Example 93.8.1. -/
def residueToDualNumber : residue Λ k ⟶ dualNumber Λ k where
  hom :=
    { toFun := fun a ↦ inl (a : k)
      map_one' := sorry
      map_mul' := sorry
      map_zero' := sorry
      map_add' := sorry
      commutes' := sorry }
  isLocalHom := sorry
  residue_compat := sorry

/-- The underlying algebra map of `residueToDualNumber` is the dual-number inclusion. -/
theorem residueToDualNumber_apply (a : (residue Λ k).carrier) :
    (residueToDualNumber Λ k).hom a = inl (a : k) := sorry

/-- The coefficient projection `k[ε] ⟶ k` in `ArtinianLocalAlgCat`. -/
def dualNumberToResidue : dualNumber Λ k ⟶ residue Λ k where
  hom :=
    { toFun := fun x ↦ x.fst
      map_one' := sorry
      map_mul' := sorry
      map_zero' := sorry
      map_add' := sorry
      commutes' := sorry }
  isLocalHom := sorry
  residue_compat := sorry

/-- The underlying algebra map of `dualNumberToResidue` is the first projection. -/
theorem dualNumberToResidue_apply (x : (dualNumber Λ k).carrier) :
    (dualNumberToResidue Λ k).hom x = x.fst := sorry

/-- The canonical `k[ε]`-algebra structure on `P[ε] = DualNumber P`. -/
def dualNumberRingHom (P : Type u) [CommRing P] [Algebra k P] :
    (dualNumber Λ k).carrier →+* DualNumber P where
  toFun x := ⟨algebraMap k P x.fst, algebraMap k P x.snd⟩
  map_one' := sorry
  map_mul' := sorry
  map_zero' := sorry
  map_add' := sorry

/-- `dualNumberRingHom` acts coefficientwise by `algebraMap k P`. -/
theorem dualNumberRingHom_apply (P : Type u) [CommRing P] [Algebra k P]
    (x : (dualNumber Λ k).carrier) :
    dualNumberRingHom Λ k P x = ⟨algebraMap k P x.fst, algebraMap k P x.snd⟩ := sorry

/-- `P[ε]` is a `k[ε]`-algebra via the coefficientwise algebra map. -/
instance instAlgebra_trivialDeformation (P : Type u) [CommRing P] [Algebra k P] :
    Algebra (dualNumber Λ k).carrier (DualNumber P) :=
  (dualNumberRingHom Λ k P).toAlgebra

/-- `P[ε]` is flat as a module over `k[ε]`. -/
instance instModuleFlat_trivialDeformation (P : Type u) [CommRing P] [Algebra k P] :
    Module.Flat (dualNumber Λ k).carrier (DualNumber P) := sorry

/-- The trivial dual-number object `(k[ε], P[ε])` of `FlatAlgebraCat`. -/
def trivialDeformationObj (P : Type u) [CommRing P] [Algebra k P] : FlatAlgebraCat Λ k :=
  of (dualNumber Λ k) (DualNumber P)

/-- The base of `trivialDeformationObj` is `k[ε]`. -/
theorem trivialDeformationObj_base (P : Type u) [CommRing P] [Algebra k P] :
    (trivialDeformationObj Λ k P).base = dualNumber Λ k := sorry

/-- The underlying algebra of `trivialDeformationObj` is `DualNumber P`. -/
theorem trivialDeformationObj_carrier (P : Type u) [CommRing P] [Algebra k P] :
    (trivialDeformationObj Λ k P).algebra = DualNumber P := sorry

/-- The trivial dual-number deformation of `x0 = (k, P)` in the fibre of `forget`. -/
def trivialDeformation (P : Type u) [CommRing P] [Algebra k P] :
    forget.Fiber (dualNumber Λ k) :=
  Fiber.mk (rfl : forget.obj (trivialDeformationObj Λ k P) = dualNumber Λ k)

/-- The underlying object of `trivialDeformation` is `trivialDeformationObj`. -/
theorem trivialDeformation_obj (P : Type u) [CommRing P] [Algebra k P] :
    Fiber.fiberInclusion.obj (trivialDeformation Λ k P) = trivialDeformationObj Λ k P := sorry

/-- The projection `P[ε] → P`, `(a, b) ↦ a`. -/
def dualNumberFstRingHom (P : Type u) [CommRing P] [Algebra k P] : DualNumber P →+* P :=
  (fstHom k P P).toRingHom

/-- `dualNumberFstRingHom` is the first projection of `DualNumber P`. -/
theorem dualNumberFstRingHom_apply (P : Type u) [CommRing P] [Algebra k P] (x : DualNumber P) :
    dualNumberFstRingHom k P x = x.fst := sorry

/-- The morphism `(k[ε], P[ε]) ⟶ (k, P)` over the coefficient projection `k[ε] ⟶ k`. -/
def trivialDeformationToResidue (P : Type u) [CommRing P] [Algebra k P] :
    trivialDeformationObj Λ k P ⟶ ofResidue Λ k P :=
  Hom.of (dualNumberToResidue Λ k) (dualNumberFstRingHom k P) sorry sorry

/-- The base map of `trivialDeformationToResidue` is `dualNumberToResidue`. -/
theorem trivialDeformationToResidue_base (P : Type u) [CommRing P] [Algebra k P] :
    forget.map (trivialDeformationToResidue Λ k P) = dualNumberToResidue Λ k := sorry

/-- The morphism `(k, P) ⟶ (k[ε], P[ε])` over the inclusion `k ⟶ k[ε]`. -/
def trivialPushforward (P : Type u) [CommRing P] [Algebra k P] :
    Fiber.fiberInclusion.obj (residueObj Λ k P) ⟶
      Fiber.fiberInclusion.obj (trivialDeformation Λ k P) :=
  Hom.of (residueToDualNumber Λ k) (inlHom P P) sorry sorry

/-- The base map of `trivialPushforward` is `residueToDualNumber`. -/
theorem trivialPushforward_base (P : Type u) [CommRing P] [Algebra k P] :
    forget.map (trivialPushforward Λ k P) = residueToDualNumber Λ k := sorry

/-- The canonical pushforward of `x0` along `k ⟶ k[ε]` is strongly cocartesian. -/
instance instIsStronglyCocartesian_trivialPushforward
    (P : Type u) [CommRing P] [Algebra k P] :
    forget.IsStronglyCocartesian (residueToDualNumber Λ k) (trivialPushforward Λ k P) := sorry

/-- The trivial deformation as an object of the residue-fibre slice `Def_P`. -/
def trivialDeformationOver (P : Type u) [CommRing P] [Algebra k P] :
    deformationCategory Λ k P :=
  Over.mk (trivialDeformationToResidue Λ k P)

/-- The trivial deformation in the dual-number fibre of `deformationForget`. -/
def trivialDeformationFiber (P : Type u) [CommRing P] [Algebra k P] :
    (deformationForget Λ k P).Fiber (dualNumber Λ k) :=
  Fiber.mk
    (rfl : (deformationForget Λ k P).obj (trivialDeformationOver Λ k P) = dualNumber Λ k)

/-- The underlying Over-object of `trivialDeformationFiber` is `trivialDeformationOver`. -/
theorem trivialDeformationFiber_obj (P : Type u) [CommRing P] [Algebra k P] :
    Fiber.fiberInclusion.obj (trivialDeformationFiber Λ k P) =
      trivialDeformationOver Λ k P := sorry

end FlatAlgebraCat
