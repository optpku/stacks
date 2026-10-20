module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.CategoryTheory.CommSq
public import Mathlib.Order.Directed
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Basic
public import ReasLib.CategoryTheory.Fibered.Groupoids.Hom.Restriction

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

/-- Data `(y_i, x, γ)` of a limit-preserving-on-objects problem over a given
directed inverse system of schemes over `S`. -/
structure Problem {X Y : GroupoidsOver S} (p : X ⟶ Y) {I : Type u} [Preorder I]
    (D : OrderDual I ⥤ Over S) (c : Cone D) (i : I) where
  /-- The object `y_i` of `Y` over `U_i`. -/
  y : Y.p.Fiber (D.obj i)
  /-- The object `x` of `X` over `U`. -/
  x : X.p.Fiber c.pt
  /-- The isomorphism `γ : p(x) ≅ y_i|_U`. -/
  γ : (fiberFunctor p c.pt).obj x ≅ restrictObj y (c.π.app i)

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

variable {X Y : GroupoidsOver S} {p : X ⟶ Y}
variable {I : Type u} [Preorder I] {D : OrderDual I ⥤ Over S} {c : Cone D} {i : I}
variable {prob : Problem p D c i}

/-- The top arrow `γ_{i'}|_U` of the restriction square, after the cartesian comparison
`p(x_{i'}|_U) ≅ p(x_{i'})|_U`. -/
def Candidate.top (cand : Candidate prob) :
    (fiberFunctor p c.pt).obj (restrictObj cand.x' (c.π.app cand.i')) ⟶
      restrictObj (restrictObj prob.y (stageHom cand.hi)) (c.π.app cand.i') :=
  (fiberFunctor_restrictObj p cand.x' (c.π.app cand.i')).hom ≫
    (restrictIso cand.γ' (c.π.app cand.i')).hom

/-- The left arrow `p(β)` of the restriction square. -/
def Candidate.left (cand : Candidate prob) :
    (fiberFunctor p c.pt).obj (restrictObj cand.x' (c.π.app cand.i')) ⟶
      (fiberFunctor p c.pt).obj prob.x :=
  (fiberFunctor p c.pt).map cand.β.hom

/-- The right arrow of the restriction square, the canonical identification of iterated
restriction with restriction along the composite cone projection. -/
def Candidate.right (cand : Candidate prob) :
    restrictObj (restrictObj prob.y (stageHom cand.hi)) (c.π.app cand.i') ⟶
      restrictObj prob.y (c.π.app i) :=
  (restrictObj_comp prob.y (stageHom cand.hi) (c.π.app cand.i') ≪≫
    restrictObj_eq prob.y (π_comp_stageHom c cand.hi)).hom

/-- The bottom arrow `γ` of the restriction square. -/
def Problem.bottom : (fiberFunctor p c.pt).obj prob.x ⟶ restrictObj prob.y (c.π.app i) :=
  prob.γ.hom

/-- The restriction square `p(x_{i'}|_U) ⟶ (y_i|_{U_{i'}})|_U` over
`p(x) ⟶ y_i|_U`. -/
def commSq (cand : Candidate prob) : Prop :=
  CommSq cand.top cand.left cand.right prob.bottom

/-- The restriction square commutes if and only if the two paths around it agree. -/
theorem commSq_iff (cand : Candidate prob) :
    commSq cand ↔ cand.left ≫ prob.bottom = cand.top ≫ cand.right := sorry

/-- A candidate is a solution when the restriction square commutes. -/
def IsSolution (cand : Candidate prob) : Prop := commSq cand

/-- Being a solution is commutativity of the restriction square. -/
theorem IsSolution_iff (cand : Candidate prob) :
    IsSolution cand ↔ commSq cand := sorry

/-- A descent problem has a solution if a candidate makes its restriction square commute. -/
def Problem.HasSolution (prob : Problem p D c i) : Prop :=
  ∃ cand : Candidate prob, IsSolution cand

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
    ∀ (i : I) (prob : Problem p D c i), prob.HasSolution

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

/-- The composition of two 1-morphisms that are limit preserving on objects is
limit preserving on objects. -/
@[stacks 06CW]
instance comp {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    (p : X ⟶ Y) (q : Y ⟶ Z) [LimitPreservingOnObjects p] [LimitPreservingOnObjects q] :
    LimitPreservingOnObjects (p ≫ q) := sorry

end LimitPreservingOnObjects

end AlgebraicGeometry.Groupoids.Hom
