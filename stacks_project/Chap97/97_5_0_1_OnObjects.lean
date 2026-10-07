module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.CategoryTheory.CommSq
public import Mathlib.Order.Directed
public import stacks_project.Chap94.Definition_94_12_1_Representable
public import stacks_project.Chap97.«97_5_0_1_Restrict»

/-!
# Limit preserving on objects

A 1-morphism of categories fibred in groupoids over `(Sch/S)_fppf` is limit preserving
on objects when every directed affine inverse-limit problem admits a solution making the
restriction square commute.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits
open CategoryTheory.Functor
open CategoryTheory.Functor.Fiber
open FiberedCategoryOver.Groupoids
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.Groupoids.Hom.LimitPreservingOnObjects

variable {S : Scheme.{u}}

/-- The bonding map `U_{i'} ⟶ U_i` of a directed inverse system, for `i ≤ i'`. -/
def stageHom {I : Type u} [Preorder I] {D : OrderDual I ⥤ Over S} {i i' : I}
    (hi : i ≤ i') : D.obj i' ⟶ D.obj i :=
  D.map (homOfLE (OrderDual.toDual_le_toDual.mpr hi))

/-- Cone projections are compatible with bonding maps of the inverse system. -/
theorem π_comp_stageHom {I : Type u} [Preorder I] {D : OrderDual I ⥤ Over S}
    (c : Cone D) {i i' : I} (hi : i ≤ i') :
    c.π.app i' ≫ stageHom hi = c.π.app i := sorry

/-- Source data `(y_i, x, γ)` of a limit-preserving-on-objects problem over a given
directed inverse system of schemes over `S`. -/
structure Problem {X Y : GroupoidsOver S} (p : X ⟶ Y) {I : Type u} [Preorder I]
    (D : OrderDual I ⥤ Over S) (c : Cone D) (i : I) where
  /-- The object `y_i` of `Y` over `U_i`. -/
  y : Y.p.Fiber (D.obj i)
  /-- The object `x` of `X` over `U`. -/
  x : X.p.Fiber c.pt
  /-- The isomorphism `γ : p(x) ≅ y_i|_U`. -/
  γ : (fiberFunctor p c.pt).obj x ≅ restrictObj y (c.π.app i)

/-- Package the source data `(y_i, x, γ)` of a limit-preserving-on-objects problem. -/
def Problem.of {X Y : GroupoidsOver S} {p : X ⟶ Y} {I : Type u} [Preorder I]
    {D : OrderDual I ⥤ Over S} {c : Cone D} {i : I} (y : Y.p.Fiber (D.obj i))
    (x : X.p.Fiber c.pt)
    (γ : (fiberFunctor p c.pt).obj x ≅ restrictObj y (c.π.app i)) :
    Problem p D c i where
  y := y
  x := x
  γ := γ

/-- The constructor `Problem.of` stores the supplied fibre object of `Y`. -/
theorem Problem.of_y {X Y : GroupoidsOver S} {p : X ⟶ Y} {I : Type u} [Preorder I]
    {D : OrderDual I ⥤ Over S} {c : Cone D} {i : I} (y : Y.p.Fiber (D.obj i))
    (x : X.p.Fiber c.pt)
    (γ : (fiberFunctor p c.pt).obj x ≅ restrictObj y (c.π.app i)) :
    (Problem.of y x γ).y = y := sorry

/-- A proposed solution tuple `(i', x_{i'}, β, γ_{i'})` to a limit-preserving-on-objects
problem, before imposing commutativity of the restriction square. -/
structure Candidate {X Y : GroupoidsOver S} {p : X ⟶ Y} {I : Type u} [Preorder I]
    {D : OrderDual I ⥤ Over S} {c : Cone D} {i : I} (prob : Problem p D c i) where
  /-- The later index `i' ≥ i`. -/
  i' : I
  /-- The inequality `i ≤ i'`. -/
  hi : i ≤ i'
  /-- The object `x_{i'}` of `X` over `U_{i'}`. -/
  x' : X.p.Fiber (D.obj i')
  /-- The isomorphism `β : x_{i'}|_U ≅ x`. -/
  β : restrictObj x' (c.π.app i') ≅ prob.x
  /-- The isomorphism `γ_{i'} : p(x_{i'}) ≅ y_i|_{U_{i'}}`. -/
  γ' : (fiberFunctor p (D.obj i')).obj x' ≅ restrictObj prob.y (stageHom hi)

/-- Package a proposed solution tuple `(i', x_{i'}, β, γ_{i'})`. -/
def Candidate.of {X Y : GroupoidsOver S} {p : X ⟶ Y} {I : Type u} [Preorder I]
    {D : OrderDual I ⥤ Over S} {c : Cone D} {i : I} {prob : Problem p D c i}
    (i' : I) (hi : i ≤ i') (x' : X.p.Fiber (D.obj i'))
    (β : restrictObj x' (c.π.app i') ≅ prob.x)
    (γ' : (fiberFunctor p (D.obj i')).obj x' ≅ restrictObj prob.y (stageHom hi)) :
    Candidate prob where
  i' := i'
  hi := hi
  x' := x'
  β := β
  γ' := γ'

/-- The constructor `Candidate.of` stores the supplied later index. -/
theorem Candidate.of_i' {X Y : GroupoidsOver S} {p : X ⟶ Y} {I : Type u} [Preorder I]
    {D : OrderDual I ⥤ Over S} {c : Cone D} {i : I} {prob : Problem p D c i}
    (i' : I) (hi : i ≤ i') (x' : X.p.Fiber (D.obj i'))
    (β : restrictObj x' (c.π.app i') ≅ prob.x)
    (γ' : (fiberFunctor p (D.obj i')).obj x' ≅ restrictObj prob.y (stageHom hi)) :
    (Candidate.of i' hi x' β γ').i' = i' := sorry

variable {X Y : GroupoidsOver S} {p : X ⟶ Y}
variable {I : Type u} [Preorder I] {D : OrderDual I ⥤ Over S} {c : Cone D} {i : I}
variable {prob : Problem p D c i}

/-- The top arrow `γ_{i'}|_U` of the source square, after the cartesian comparison
`p(x_{i'}|_U) ≅ p(x_{i'})|_U`. -/
def top (cand : Candidate prob) :
    (fiberFunctor p c.pt).obj (restrictObj cand.x' (c.π.app cand.i')) ⟶
      restrictObj (restrictObj prob.y (stageHom cand.hi)) (c.π.app cand.i') :=
  (fiberFunctor_restrictObj p cand.x' (c.π.app cand.i')).hom ≫
    (restrictIso cand.γ' (c.π.app cand.i')).hom

/-- The left arrow `p(β)` of the source square. -/
def left (cand : Candidate prob) :
    (fiberFunctor p c.pt).obj (restrictObj cand.x' (c.π.app cand.i')) ⟶
      (fiberFunctor p c.pt).obj prob.x :=
  (fiberFunctor p c.pt).map cand.β.hom

/-- The right arrow of the source square, the canonical identification of iterated
restriction with restriction along the composite cone projection. -/
def right (cand : Candidate prob) :
    restrictObj (restrictObj prob.y (stageHom cand.hi)) (c.π.app cand.i') ⟶
      restrictObj prob.y (c.π.app i) :=
  (restrictObj_comp prob.y (stageHom cand.hi) (c.π.app cand.i') ≪≫
    restrictObj_eq prob.y (π_comp_stageHom c cand.hi)).hom

/-- The bottom arrow `γ` of the source square. -/
def bottom : (fiberFunctor p c.pt).obj prob.x ⟶ restrictObj prob.y (c.π.app i) :=
  prob.γ.hom

/-- The source commuting square `p(x_{i'}|_U) ⟶ (y_i|_{U_{i'}})|_U` over
`p(x) ⟶ y_i|_U`. -/
def commSq (cand : Candidate prob) : Prop :=
  CommSq (top cand) (left cand) (right cand) bottom

/-- The source square commutes if and only if the two paths around it agree. -/
theorem commSq_iff (cand : Candidate prob) :
    commSq cand ↔ left cand ≫ bottom = top cand ≫ right cand := sorry

/-- A candidate is a solution when the source restriction square commutes. -/
def IsSolution (cand : Candidate prob) : Prop := commSq cand

/-- Being a solution is commutativity of the source square. -/
theorem IsSolution_iff (cand : Candidate prob) :
    IsSolution cand ↔ commSq cand := sorry

end AlgebraicGeometry.Groupoids.Hom.LimitPreservingOnObjects

namespace AlgebraicGeometry.Groupoids.Hom

open LimitPreservingOnObjects

/-- A 1-morphism of categories fibred in groupoids over `(Sch/S)_fppf` is limit preserving
on objects when every directed affine inverse-limit problem admits a solution making the
restriction square commute. -/
class LimitPreservingOnObjects {S : Scheme.{u}} {X Y : GroupoidsOver S} (p : X ⟶ Y) :
    Prop where
  /-- Every directed affine inverse-limit problem admits a commuting solution. -/
  exists_solution : ∀ {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (D : OrderDual I ⥤ Over S) (c : Cone D), IsLimit c →
    (∀ i : I, IsAffine (D.obj i).left) → IsAffine c.pt.left →
    ∀ (i : I) (prob : Problem p D c i), ∃ cand : Candidate prob, IsSolution cand

namespace LimitPreservingOnObjects

/-- The identity 1-morphism is limit preserving on objects. -/
instance id {S : Scheme.{u}} {X : GroupoidsOver S} :
    LimitPreservingOnObjects (𝟙 X) := sorry

/-- A limit-preserving-on-objects 1-morphism admits a solution for every directed affine
inverse-limit problem. -/
theorem spec {S : Scheme.{u}} {X Y : GroupoidsOver S} (p : X ⟶ Y)
    [LimitPreservingOnObjects p] {I : Type u} [Preorder I] [Nonempty I]
    [IsDirected I (· ≤ ·)] (D : OrderDual I ⥤ Over S) (c : Cone D) (hc : IsLimit c)
    (hD : ∀ i : I, IsAffine (D.obj i).left) (hpt : IsAffine c.pt.left) (i : I)
    (prob : Problem p D c i) : ∃ cand : Candidate prob, IsSolution cand := sorry

end LimitPreservingOnObjects

end AlgebraicGeometry.Groupoids.Hom
