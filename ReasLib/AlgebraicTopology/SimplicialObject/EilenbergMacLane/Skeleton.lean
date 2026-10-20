/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicTopology.SimplicialObject.EilenbergMacLane.Truncation
public import ReasLib.AlgebraicTopology.SimplexCategory.Truncated.KanExtension.FiniteConnected
public import ReasLib.AlgebraicTopology.SimplicialObject.Truncated.Skeleton.Skeletal

/-!
@stack 0191

# Skeleton model of Eilenberg-MacLane simplicial objects

The left Kan extension of a truncated object concentrated in degree `k` is canonically the
Eilenberg-MacLane object `K(B, k)`. The objectwise comparison requires only the chosen pointwise
skeleton of that concentrated object. Uniform skeleton existence enters only when these
comparisons are assembled naturally in the coefficient object.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open HomologicalComplex
open scoped Simplicial

noncomputable section

universe v u

namespace CategoryTheory.SimplicialObject.eilenbergMacLane.skeleton

variable {A : Type u} [Category.{v} A] [Preadditive A] [HasZeroObject A]
  [HasFiniteCoproducts A]

variable (k : ℕ)

section Objectwise

variable (B : A)
variable [SimplicialObject.Truncated.HasPointwiseSkeleton
  (Truncated.concentrated B k)]

/-- The explicit inverse component from the Dold-Kan coproduct model to the skeleton extension.
Only summands landing in degree `k` contribute. -/
@[stacks 0191 "Eilenberg-MacLane skeleton inverse component"]
noncomputable def invApp (Δ : SimplexCategoryᵒᵖ) :
    (eilenbergMacLane B k).obj Δ ⟶
      (Truncated.concentrated B k).skeleton.obj Δ :=
  (AlgebraicTopology.DoldKan.Γ₀.splitting
    ((single A (ComplexShape.down ℕ) k).obj B)).desc Δ fun a ↦
      if hA : a.1.unop.len = k then
        (singleObjXIsoOfEq (ComplexShape.down ℕ) k B a.1.unop.len hA).hom ≫
          eqToHom (if_pos hA).symm ≫
          ((SimplexCategory.Truncated.inclusion k).op.leftKanExtensionUnit
            (Truncated.concentrated B k)).app
              (Opposite.op ⟨a.1.unop, hA.le⟩) ≫
          (Truncated.concentrated B k).skeleton.map a.e.op
      else 0

/-- The forward skeleton comparison in a fixed simplicial degree, obtained from the universal
descent of the truncation comparison. -/
@[stacks 0191 "Eilenberg-MacLane skeleton forward component"]
noncomputable def homApp (Δ : SimplexCategoryᵒᵖ) :
    (Truncated.concentrated B k).skeleton.obj Δ ⟶
      (eilenbergMacLane B k).obj Δ :=
  (Truncated.skeleton.desc (Truncated.concentrated B k)
    (eilenbergMacLane B k) (eilenbergMacLane.truncation.objIso B k).hom).app Δ

/-- The forward skeleton comparison components are natural in simplex operators. -/
@[stacks 0191 "Eilenberg-MacLane skeleton forward naturality"]
theorem homApp.naturality {Δ Δ' : SimplexCategoryᵒᵖ} (f : Δ ⟶ Δ') :
    (Truncated.concentrated B k).skeleton.map f ≫ homApp k B Δ' =
      homApp k B Δ ≫ (eilenbergMacLane B k).map f := sorry

/-- The skeleton comparison from the left Kan extension to the Eilenberg-MacLane object. -/
@[stacks 0191 "Eilenberg-MacLane skeleton comparison"]
noncomputable def hom :
    (Truncated.concentrated B k).skeleton ⟶ eilenbergMacLane B k :=
  Truncated.skeleton.desc (Truncated.concentrated B k)
    (eilenbergMacLane B k) (eilenbergMacLane.truncation.objIso B k).hom

/-- Restricting the forward skeleton comparison along the skeleton unit recovers the
truncation comparison. -/
@[reassoc (attr := simp), stacks 0191 "Eilenberg-MacLane skeleton unit forward formula"]
theorem unit_hom :
    Truncated.skeleton.unit (Truncated.concentrated B k) ≫
        (SimplexCategory.Truncated.inclusion k).op.whiskerLeft (hom k B) =
      (eilenbergMacLane.truncation.objIso B k).hom := sorry

/-- The component of the forward skeleton comparison is `homApp`. -/
@[simp, stacks 0191 "Eilenberg-MacLane skeleton forward component formula"]
theorem hom_app (Δ : SimplexCategoryᵒᵖ) :
    (hom k B).app Δ = homApp k B Δ := sorry

/-- The inverse skeleton comparison components are natural in simplex operators. -/
@[stacks 0191 "Eilenberg-MacLane skeleton inverse naturality"]
theorem invApp.naturality {Δ Δ' : SimplexCategoryᵒᵖ} (f : Δ ⟶ Δ') :
    (eilenbergMacLane B k).map f ≫ invApp k B Δ' =
      invApp k B Δ ≫
        (Truncated.concentrated B k).skeleton.map f := sorry

/-- The inverse skeleton comparison assembled from its explicit coproduct components. -/
@[stacks 0191 "Eilenberg-MacLane skeleton inverse"]
noncomputable def inv :
    eilenbergMacLane B k ⟶ (Truncated.concentrated B k).skeleton where
  app := invApp k B
  naturality _ _ f := invApp.naturality k B f

/-- The inverse truncation comparison followed by the skeleton unit is the restriction of the
inverse skeleton comparison. -/
@[reassoc (attr := simp), stacks 0191 "Eilenberg-MacLane skeleton inverse unit formula"]
theorem inv_unit :
    (eilenbergMacLane.truncation.objIso B k).inv ≫
        Truncated.skeleton.unit (Truncated.concentrated B k) =
      (SimplexCategory.Truncated.inclusion k).op.whiskerLeft (inv k B) := sorry

/-- The component of the inverse skeleton comparison is `invApp`. -/
@[simp, stacks 0191 "Eilenberg-MacLane skeleton inverse component formula"]
theorem inv_app (Δ : SimplexCategoryᵒᵖ) :
    (inv k B).app Δ = invApp k B Δ := sorry

/-- The skeleton comparison followed by its explicit inverse is the identity. -/
@[simp, stacks 0191 "forward-inverse law for the Eilenberg-MacLane skeleton comparison"]
theorem hom_comp_inv : hom k B ≫ inv k B = 𝟙 _ := sorry

/-- The explicit inverse followed by the skeleton comparison is the identity. -/
@[simp, stacks 0191 "inverse-forward law for the Eilenberg-MacLane skeleton comparison"]
theorem inv_comp_hom : inv k B ≫ hom k B = 𝟙 _ := sorry

/-- The skeleton extension of a concentrated object is explicitly isomorphic to its canonical
Eilenberg-MacLane object. -/
@[stacks 0191 "skeleton model of the Eilenberg-MacLane object"]
noncomputable def objIso :
    (Truncated.concentrated B k).skeleton ≅ eilenbergMacLane B k where
  hom := hom k B
  inv := inv k B
  hom_inv_id := hom_comp_inv k B
  inv_hom_id := inv_comp_hom k B

/-- The forward map of `objIso` is the canonical skeleton comparison. -/
@[simp, stacks 0191 "Eilenberg-MacLane skeleton isomorphism forward map"]
theorem objIso.hom : (objIso k B).hom = hom k B := sorry

/-- The inverse map of `objIso` is the explicit coproduct comparison. -/
@[simp, stacks 0191 "Eilenberg-MacLane skeleton isomorphism inverse map"]
theorem objIso.inv : (objIso k B).inv = inv k B := sorry

end Objectwise

section Functorial

variable [SimplicialObject.Truncated.HasPointwiseSkeletons A k]

/-- The objectwise skeleton comparisons are natural in the coefficient object. -/
@[stacks 0191 "naturality of the Eilenberg-MacLane skeleton comparison"]
theorem objIso.hom_naturality {B D : A} (f : B ⟶ D) :
    (Truncated.concentrated.functor (A := A) k ⋙ Truncated.sk k).map f ≫
        (objIso k D).hom =
      (objIso k B).hom ≫ (eilenbergMacLane.functor k).map f := sorry

/-- The inverse objectwise skeleton comparisons are natural in the coefficient object. -/
@[stacks 0191 "inverse naturality of the Eilenberg-MacLane skeleton comparison"]
theorem objIso.inv_naturality {B D : A} (f : B ⟶ D) :
    (eilenbergMacLane.functor k).map f ≫ (objIso k D).inv =
      (objIso k B).inv ≫
        (Truncated.concentrated.functor (A := A) k ⋙ Truncated.sk k).map f := sorry

/-- Skeleton extensions of concentrated objects are naturally isomorphic to the
Eilenberg-MacLane functor. -/
@[stacks 0191 "functorial skeleton model of Eilenberg-MacLane objects"]
noncomputable def iso :
    Truncated.concentrated.functor (A := A) k ⋙ Truncated.sk k ≅
      eilenbergMacLane.functor k :=
  NatIso.ofComponents (fun B ↦ objIso k B) (fun f ↦ objIso.hom_naturality k f)

/-- The component of the functorial skeleton comparison is the explicit objectwise
isomorphism. -/
@[simp, stacks 0191 "functorial Eilenberg-MacLane skeleton component formula"]
theorem iso_app (B : A) :
    (iso (A := A) k).app B = objIso k B := sorry

end Functorial

end CategoryTheory.SimplicialObject.eilenbergMacLane.skeleton

namespace CategoryTheory.SimplicialObject.eilenbergMacLane

variable {A : Type u} [Category.{v} A] [Preadditive A] [HasZeroObject A]
  [HasFiniteCoproducts A]

/-- The Eilenberg-MacLane simplicial object `K(B, k)` is intrinsically `k`-skeletal. -/
@[stacks 0191 "Eilenberg-MacLane objects are skeletal"]
instance isSkeletal (B : A) (k : ℕ) :
    (eilenbergMacLane B k).IsSkeletal k := sorry

variable (B : A) (k : ℕ)

end CategoryTheory.SimplicialObject.eilenbergMacLane
