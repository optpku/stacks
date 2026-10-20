/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.CochainDGAlgebra.Homology
public import ReasLib.Algebra.Homology.DifferentialGradedModule.Bimodule.Derived
public import ReasLib.Algebra.Homology.DifferentialGradedModule.Shift.Category
public import Mathlib.CategoryTheory.Localization.Linear
public import Mathlib.CategoryTheory.Shift.ShiftedHom
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Self-Extensions Induced by a Differential Graded Bimodule Action

The left action of a differential graded `(A, B)`-bimodule sends a class in `H^k(A)` to a
shifted self-map of its underlying right `B`-module.  This leaf constructs that map before and
after any shift-compatible localization and records independence from the chosen cycle.
-/

@[expose] public section

noncomputable section

universe u v w

open CategoryTheory
open DifferentialGradedCategory
open scoped DifferentialGradedCategory DifferentialGradedModule

namespace DifferentialGradedBimodule

variable {R : Type u} [CommRing R]
variable {A B : CochainDGAlgebra.{u, v} R}

/-- The homogeneous right-`B`-linear self-map defined by the left action of an element of `A`. -/
@[stacks 09S7 "homogeneous self-map from the left DGA action"]
def leftActionGradedHom (N : DifferentialGradedBimodule.{u, v, v, v} A B)
    (k : ℤ) (a : A.X k) :
    DifferentialGradedModule.GradedHom B N.toRightModule N.toRightModule k :=
  ⟨fun p ↦ ModuleCat.castLinearMap (congrArg N.X (add_comm k p)) (N.leftMul k p a), sorry⟩

/-- A cycle of `A` acts by a closed homogeneous self-map of the underlying right module. -/
@[stacks 09S7 "closed graded self-map from a cycle"]
def leftActionClosedGradedHom (N : DifferentialGradedBimodule.{u, v, v, v} A B)
    (k : ℤ) (z : A.cycles k) :
    DifferentialGradedModule.ClosedGradedHom B N.toRightModule N.toRightModule k :=
  ⟨N.leftActionGradedHom k (ModuleCat.Hom.hom (A.iCycles k) z), sorry⟩

/-- A cycle of `A` acts by a morphism from the underlying right module to its shift. -/
@[stacks 09S7 "shifted module self-map from a cycle"]
def leftActionHom (N : DifferentialGradedBimodule.{u, v, v, v} A B)
    (k : ℤ) (z : A.cycles k) : N.toRightModule ⟶ N.toRightModule[k] :=
  DifferentialGradedModule.closedGradedHomEquivShiftHom
    B N.toRightModule N.toRightModule k (N.leftActionClosedGradedHom k z)

/-- The explicit module shift and the categorical shift of the underlying homotopy object agree.
This is definitional for the induced shift structure. -/
@[stacks 09S7 "module-to-homotopy shift comparison"]
def rightHomotopyShiftIso (N : DifferentialGradedBimodule.{u, v, v, v} A B) (k : ℤ) :
    (DifferentialGradedModule.toK.{u, v} B).obj N.toRightModule[k] ≅
      N.rightHomotopyObject⟦k⟧ :=
  ((DifferentialGradedModule.toK.{u, v} B).commShiftIso k).app N.toRightModule

/-- The homotopy-class self-map induced by the action of a cycle of `A`. -/
@[stacks 09S7 "homotopy self-map from the left action"]
def leftActionHomotopy (N : DifferentialGradedBimodule.{u, v, v, v} A B)
    (k : ℤ) (z : A.cycles k) :
    N.rightHomotopyObject ⟶ N.rightHomotopyObject⟦k⟧ :=
  (DifferentialGradedModule.toK.{u, v} B).map (N.leftActionHom k z) ≫
    (N.rightHomotopyShiftIso k).hom

/-- After a shift-compatible functor, a cycle of `A` acts on the image of the underlying right
module by a shifted self-map. -/
@[stacks 09S7 "localized shifted self-map from the left action"]
def leftActionMap {D : Type w} [Category D] [HasShift D ℤ]
    (Q : K R (DifferentialGradedModule.{u, v} B) ⥤ D) [Q.CommShift ℤ]
    (N : DifferentialGradedBimodule.{u, v, v, v} A B) (k : ℤ) (z : A.cycles k) :
    Q.obj N.rightHomotopyObject ⟶ (Q.obj N.rightHomotopyObject)⟦k⟧ :=
  ShiftedHom.map (N.leftActionHomotopy k z) Q

/-- The degree-`k` shifted endomorphisms of the image of a differential graded bimodule. -/
@[stacks 09S7 "shifted self-extension object"]
abbrev selfExt {D : Type w} [Category D] [HasShift D ℤ]
    (Q : K R (DifferentialGradedModule.{u, v} B) ⥤ D)
    (N : DifferentialGradedBimodule.{u, v, v, v} A B) (k : ℤ) :=
  Q.obj N.rightHomotopyObject ⟶ (Q.obj N.rightHomotopyObject)⟦k⟧

/-- Lemma 22.37.2 (09S7): the canonical `R`-linear map
`H^k(A) ⟶ Hom(Q(N), Q(N)[k])` induced by the left `A`-action on a differential graded
`(A, B)`-bimodule. -/
@[stacks 09S7 "self-extension map induced by a differential graded bimodule action"]
noncomputable def selfExtMap {D : Type w}
    [Category D] [Preadditive D] [Linear R D] [HasShift D ℤ]
    (Q : K R (DifferentialGradedModule.{u, v} B) ⥤ D)
    [Q.CommShift ℤ] [Q.Additive] [Q.Linear R]
    (N : DifferentialGradedBimodule.{u, v, v, v} A B) (k : ℤ) :
    A.homology k →ₗ[R] N.selfExt Q k where
  toFun := fun x ↦ N.leftActionMap Q k (A.homologyCycle k x)
  map_add' := sorry
  map_smul' := sorry

/-- Every self-extension comparison induced by the left action of `N` is bijective after the
chosen additive, shift-compatible `R`-linear functor `Q`. -/
@[stacks 09S7 "self-extension comparison after a chosen localization"]
def HasSelfExtComparisonFor {D : Type w}
    [Category D] [Preadditive D] [Linear R D] [HasShift D ℤ]
    (N : DifferentialGradedBimodule.{u, v, v, v} A B)
    (Q : K R (DifferentialGradedModule.{u, v} B) ⥤ D)
    [Q.CommShift ℤ] [Q.Additive] [Q.Linear R] : Prop :=
  ∀ k : ℤ, Function.Bijective (N.selfExtMap Q k)

/-- A chosen self-extension comparison is bijective in every degree. -/
@[stacks 09S7 "degreewise bijectivity of a self-extension comparison",
  stacks 09R9 "degreewise canonical self-extension bijectivity"]
theorem HasSelfExtComparisonFor.bijective {D : Type w}
    [Category D] [Preadditive D] [Linear R D] [HasShift D ℤ]
    {N : DifferentialGradedBimodule.{u, v, v, v} A B}
    {Q : K R (DifferentialGradedModule.{u, v} B) ⥤ D}
    [Q.CommShift ℤ] [Q.Additive] [Q.Linear R]
    (h : N.HasSelfExtComparisonFor Q) (k : ℤ) :
    Function.Bijective (N.selfExtMap Q k) := sorry

/-- Every canonical self-extension comparison induced by the left action of `N` is bijective. -/
@[stacks 09R9 "self-extension comparison for a DG bimodule", stacks 09S7]
def HasSelfExtComparison (N : DifferentialGradedBimodule.{u, v, v, v} A B) : Prop :=
  N.HasSelfExtComparisonFor (DifferentialGradedModule.Derived.Q.{u, v} B)

/-- The canonical self-extension comparison is bijective in every degree. -/
@[stacks 09R9 "canonical self-extension bijectivity", stacks 09S7]
theorem HasSelfExtComparison.bijective
    {N : DifferentialGradedBimodule.{u, v, v, v} A B}
    (h : N.HasSelfExtComparison) (k : ℤ) :
    Function.Bijective
      (N.selfExtMap (DifferentialGradedModule.Derived.Q.{u, v} B) k) := sorry

/-- The self-extension map is computed from the controlled cycle representative. -/
@[stacks 09S7 "self-extension map evaluation"]
theorem selfExtMap_apply {D : Type w}
    [Category D] [Preadditive D] [Linear R D] [HasShift D ℤ]
    (Q : K R (DifferentialGradedModule.{u, v} B) ⥤ D)
    [Q.CommShift ℤ] [Q.Additive] [Q.Linear R]
    (N : DifferentialGradedBimodule.{u, v, v, v} A B) (k : ℤ) (x : A.homology k) :
    N.selfExtMap Q k x = N.leftActionMap Q k (A.homologyCycle k x) := sorry

/-- Cycles representing the same homology class induce the same shifted self-map in the
homotopy category. -/
@[stacks 09S7 "cycle-independence in the homotopy category"]
theorem leftActionHomotopy_eq_of_homologyπ_eq
    (N : DifferentialGradedBimodule.{u, v, v, v} A B) (k : ℤ) (z z' : A.cycles k)
    (h : ModuleCat.Hom.hom (A.homologyπ k) z =
      ModuleCat.Hom.hom (A.homologyπ k) z') :
    N.leftActionHomotopy k z = N.leftActionHomotopy k z' := sorry

/-- Cycles representing the same homology class induce the same localized shifted self-map. -/
@[stacks 09S7 "cycle-independence after localization"]
theorem leftActionMap_eq_of_homologyπ_eq {D : Type w} [Category D] [HasShift D ℤ]
    (Q : K R (DifferentialGradedModule.{u, v} B) ⥤ D) [Q.CommShift ℤ]
    (N : DifferentialGradedBimodule.{u, v, v, v} A B) (k : ℤ) (z z' : A.cycles k)
    (h : ModuleCat.Hom.hom (A.homologyπ k) z =
      ModuleCat.Hom.hom (A.homologyπ k) z') :
    N.leftActionMap Q k z = N.leftActionMap Q k z' := sorry

/-- Any cycle representing `x` computes the canonical self-extension map at `x`. -/
@[stacks 09S7 "cycle representative formula for self-extension"]
theorem selfExtMap_eq_leftActionMap {D : Type w}
    [Category D] [Preadditive D] [Linear R D] [HasShift D ℤ]
    (Q : K R (DifferentialGradedModule.{u, v} B) ⥤ D)
    [Q.CommShift ℤ] [Q.Additive] [Q.Linear R]
    (N : DifferentialGradedBimodule.{u, v, v, v} A B) (k : ℤ)
    (x : A.homology k) (z : A.cycles k)
    (hz : ModuleCat.Hom.hom (A.homologyπ k) z = x) :
    N.selfExtMap Q k x = N.leftActionMap Q k z := sorry

/-- A bijective canonical self-extension map, exposed as an `R`-linear equivalence for downstream
transport. -/
@[stacks 09S7 "linear equivalence from a bijective self-extension map",
  stacks 09R9 "linear self-extension comparison equivalence"]
noncomputable def selfExtLinearEquiv {D : Type w}
    [Category D] [Preadditive D] [Linear R D] [HasShift D ℤ]
    (Q : K R (DifferentialGradedModule.{u, v} B) ⥤ D)
    [Q.CommShift ℤ] [Q.Additive] [Q.Linear R]
    (N : DifferentialGradedBimodule.{u, v, v, v} A B) (k : ℤ)
    (h : Function.Bijective (N.selfExtMap Q k)) :
    A.homology k ≃ₗ[R] N.selfExt Q k :=
  LinearEquiv.ofBijective (N.selfExtMap Q k) h

/-- The forward map of `selfExtLinearEquiv` is the canonical self-extension comparison. -/
@[stacks 09S7 "forward map of the self-extension equivalence", simp]
theorem selfExtLinearEquiv_apply {D : Type w}
    [Category D] [Preadditive D] [Linear R D] [HasShift D ℤ]
    (Q : K R (DifferentialGradedModule.{u, v} B) ⥤ D)
    [Q.CommShift ℤ] [Q.Additive] [Q.Linear R]
    (N : DifferentialGradedBimodule.{u, v, v, v} A B) (k : ℤ)
    (h : Function.Bijective (N.selfExtMap Q k)) (x : A.homology k) :
    selfExtLinearEquiv Q N k h x = N.selfExtMap Q k x := sorry

/-- A self-extension comparison in every degree supplies a canonical linear equivalence in each
degree. -/
@[stacks 09S7 "degreewise self-extension linear equivalence",
  stacks 09R9 "canonical degreewise self-extension equivalence"]
noncomputable def HasSelfExtComparisonFor.linearEquiv {D : Type w}
    [Category D] [Preadditive D] [Linear R D] [HasShift D ℤ]
    {Q : K R (DifferentialGradedModule.{u, v} B) ⥤ D}
    [Q.CommShift ℤ] [Q.Additive] [Q.Linear R]
    {N : DifferentialGradedBimodule.{u, v, v, v} A B}
    (h : N.HasSelfExtComparisonFor Q) (k : ℤ) :
    A.homology k ≃ₗ[R] N.selfExt Q k :=
  selfExtLinearEquiv Q N k (h.bijective k)

/-- The degreewise linear equivalence supplied by a self-extension comparison acts by the
canonical self-extension map. -/
@[stacks 09S7 "evaluation of the self-extension linear equivalence",
  stacks 09R9, simp]
theorem HasSelfExtComparisonFor.linearEquiv_apply {D : Type w}
    [Category D] [Preadditive D] [Linear R D] [HasShift D ℤ]
    {Q : K R (DifferentialGradedModule.{u, v} B) ⥤ D}
    [Q.CommShift ℤ] [Q.Additive] [Q.Linear R]
    {N : DifferentialGradedBimodule.{u, v, v, v} A B}
    (h : N.HasSelfExtComparisonFor Q) (k : ℤ) (x : A.homology k) :
    h.linearEquiv k x = N.selfExtMap Q k x := sorry

end DifferentialGradedBimodule
