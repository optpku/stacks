/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicTopology.SimplicialObject.InternalHom.Finiteness
public import ReasLib.AlgebraicTopology.SimplicialObject.InternalHom.RepresentableBy.Variance
public import ReasLib.AlgebraicTopology.SimplicialObject.InternalHom.Pushout.IsPullback
public import ReasLib.AlgebraicTopology.SimplicialSet.Subcomplex.AdjoinSimplex
public import ReasLib.AlgebraicTopology.SimplicialSet.Subcomplex.Filtration.Finite
public import ReasLib.CategoryTheory.Sites.Hypercovering.FixedTarget
public import ReasLib.CategoryTheory.Sites.Hypercovering.Category
public import ReasLib.CategoryTheory.Sites.Hypercovering.Refinement

/-!
# Restriction maps on internal homs into hypercoverings

The reusable core is the covering property for restriction across a simplicial cell attachment.
Single-simplex extensions and finite subcomplex inclusions are its canonical simplicial-set
specializations.
-/

@[expose] public section

noncomputable section

universe w v u

namespace CategoryTheory.Hypercovering.InternalHom

open CategoryTheory.Limits Opposite
open SemiRepresentableFamily.OverFamily
open scoped CategoryTheory.SemiRepresentableFamily Simplicial

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [HasPullbacks C] {X : C}

namespace PrecompZero

/-- Restriction in degree zero along a finite nonempty simplicial cell attachment is a covering
morphism for every hypercovering. This pushout formulation is the reusable engine behind
single-simplex extensions. -/
@[stacks 01GM "internal-hom restriction across a simplicial cell attachment"]
theorem ofBoundaryPushout
    {U V : SSet.{w}} [U.Finite] [V.Finite] [U.Nonempty] [V.Nonempty]
    (a : U ⟶ V) (n : ℕ) (b : ∂Δ[n].toSSet ⟶ U) (c : Δ[n] ⟶ V)
    (square : IsPushout ∂Δ[n].ι b c a) (K : Hypercovering.{w} J X)
    {MU MV : SimplicialObject (SemiRepresentableFamily.OverFamily.{v, u, w} X)}
    (RU : (SimplicialObject.internalHom.presheaf U K.toSimplicialObject).RepresentableBy MU)
    (RV : (SimplicialObject.internalHom.presheaf V K.toSimplicialObject).RepresentableBy MV) :
    SemiRepresentableFamily.OverFamily.covering J
      ((SimplicialObject.internalHom.precompOf a RU RV).app (op ⦋0⦌)) := sorry

/-- Restriction in degree zero along a degreewise single-simplex extension is a covering
morphism for every hypercovering. -/
@[stacks 01GM "internal-hom restriction across a single-simplex extension"]
theorem ofSingleSimplex
    {V : SSet.{w}} [V.Finite] (U : V.Subcomplex) [U.toSSet.Nonempty] [V.Nonempty]
    {n : ℕ} {x : V _⦋n⦌} (h : SSet.Subcomplex.singleSimplex.Degreewise U n x)
    (K : Hypercovering.{w} J X)
    {MU MV : SimplicialObject (SemiRepresentableFamily.OverFamily.{v, u, w} X)}
    (RU : (SimplicialObject.internalHom.presheaf U K.toSimplicialObject).RepresentableBy MU)
    (RV : (SimplicialObject.internalHom.presheaf V K.toSimplicialObject).RepresentableBy MV) :
    SemiRepresentableFamily.OverFamily.covering J
      ((SimplicialObject.internalHom.precompOf U.ι RU RV).app (op ⦋0⦌)) := sorry

/-- Restriction in degree zero along an inclusion of finite nonempty simplicial sets is a
covering morphism for every hypercovering. -/
@[stacks 01GN "internal-hom restriction along a finite subcomplex inclusion"]
theorem isCovering
    {V : SSet.{w}} [V.Finite] (U : V.Subcomplex) [U.toSSet.Nonempty] [V.Nonempty]
    (K : Hypercovering.{w} J X)
    {MU MV : SimplicialObject (SemiRepresentableFamily.OverFamily.{v, u, w} X)}
    (RU : (SimplicialObject.internalHom.presheaf U K.toSimplicialObject).RepresentableBy MU)
    (RV : (SimplicialObject.internalHom.presheaf V K.toSimplicialObject).RepresentableBy MV) :
    SemiRepresentableFamily.OverFamily.covering J
      ((SimplicialObject.internalHom.precompOf U.ι RU RV).app (op ⦋0⦌)) := sorry

end PrecompZero

/-- A map on a copower indexed by `V` extends a boundary datum after refinement when its
restriction along `U.ι` agrees with the datum pulled back along the refining hypercovering map. -/
@[stacks 01GT "extension after hypercovering refinement"]
def IsRefinementExtension {V : SSet.{w}} (U : V.Subcomplex)
    {K L K' : Hypercovering.{w} J X}
    (a : SimplicialObject.copower U K.toSimplicialObject ⟶ L.toSimplicialObject)
    (c : K' ⟶ K)
    (g : SimplicialObject.copower V K'.toSimplicialObject ⟶ L.toSimplicialObject) : Prop :=
  SimplicialObject.copower.indexHom K'.toSimplicialObject U.ι ≫ g =
    SimplicialObject.copower.hom U (Hypercovering.Hom.toSimplicial c) ≫ a

namespace IsRefinementExtension

/-- Remark 25.9.3 (Tag 01GT), at the reusable finite-subcomplex level: a map defined on a
finite simplicial subcomplex extends across the ambient finite simplicial set after refining
the hypercovering in its source. -/
@[stacks 01GT "finite simplicial extension after hypercovering refinement"]
theorem existsOfFinite
    {V : SSet.{w}} [V.Finite] (U : V.Subcomplex)
    {K L : Hypercovering.{w} J X}
    (a : SimplicialObject.copower U K.toSimplicialObject ⟶ L.toSimplicialObject) :
    ∃ (K' : Hypercovering.{w} J X) (c : K' ⟶ K)
      (g : SimplicialObject.copower V K'.toSimplicialObject ⟶ L.toSimplicialObject),
      IsRefinementExtension U a c g := sorry

/-- Remark 25.9.3 (Tag 01GT): a map defined on the boundary of a standard simplex extends
across that simplex after refining the hypercovering in its source. -/
@[stacks 01GT "standard-simplex boundary extension after refinement"]
theorem existsBoundary
    (k : ℕ) {K L : Hypercovering.{w} J X}
    (a : SimplicialObject.copower
      (∂Δ[k] : (Δ[k] : SSet.{w}).Subcomplex) K.toSimplicialObject ⟶
        L.toSimplicialObject) :
    ∃ (K' : Hypercovering.{w} J X) (c : K' ⟶ K)
      (g : SimplicialObject.copower (Δ[k] : SSet.{w}) K'.toSimplicialObject ⟶
        L.toSimplicialObject),
      IsRefinementExtension
        (∂Δ[k] : (Δ[k] : SSet.{w}).Subcomplex) a c g := sorry

end IsRefinementExtension

end CategoryTheory.Hypercovering.InternalHom
