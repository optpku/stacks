module

public import ReasLib.CategoryTheory.Fibered.CartesianBasedFunctor.Basic
public import ReasLib.CategoryTheory.Fibered.CartesianBasedFunctor.Cospan
public import ReasLib.CategoryTheory.Fibered.Cleavage.Basic.Intrinsic
public import ReasLib.CategoryTheory.Fibered.PseudoPullback.Functoriality.Map.Construction
public import ReasLib.CategoryTheory.Fibered.PseudoPullback.Projections
import Mathlib.Tactic.CrossRefAttribute

/-!
# Cartesian structure on explicit pseudo-pullbacks

The explicit pseudo-pullback in `Cat/C` preserves fibredness and strongly-cartesian structure
under cartesian based functors.  This layer belongs to the concrete pseudo-pullback owner, rather
than to any particular locally induced bicategory.
-/

@[expose] public section

universe u v w vB uX vX uY vY uS vS uT vT
universe uX₁ vX₁ uY₁ vY₁ uS₁ vS₁ uX₂ vX₂ uY₂ vY₂ uS₂ vS₂

namespace CategoryTheory

open scoped Bicategory BasedFunctor

variable {C : Type u} [Category.{v} C]

namespace BasedCategory
namespace PseudoPullback

variable {X : BasedCategory.{vX, uX} C} {Y : BasedCategory.{vY, uY} C}
variable {S : BasedCategory.{vS, uS} C}

/-
The closure results belong to the explicit iso-comma construction itself, independently of the
particular locally induced bicategory in which it is later used. When the common target is also
fibred, this is the computational form of the indexed-category statement that pointwise iso-comma
categories of cartesian functors again assemble into a fibration. The Grothendieck correspondence
supplies the invariant interpretation; the concrete `BasedCategory.PseudoPullback` remains the
data owner so that objects, morphisms, and projections retain useful definitional equalities.
-/

/-- The projection of the pseudo-pullback of two cartesian based functors with fibred domains is
fibred; the common target need not itself be fibred. This is canonical and is therefore available
to typeclass search. -/
@[stacks 0040 "fibredness of an explicit pseudo-pullback projection"]
instance projectionIsFibered
    [X.p.IsFibered] [Y.p.IsFibered]
    (F : CartesianBasedFunctor X.p S.p) (G : CartesianBasedFunctor Y.p S.p) :
    (BasedCategory.PseudoPullback F.toBasedFunctor G.toBasedFunctor).p.IsFibered := sorry
/- Proof strategy: apply `Functor.IsFibered.of_exists_isStronglyCartesian`. For a base arrow into
a pseudo-pullback object, choose strongly cartesian lifts of its two components in `X` and `Y`.
The fields `F.preservesStronglyCartesian` and `G.preservesStronglyCartesian` map these lifts to
strongly cartesian arrows in `S`; uniqueness of such lifts supplies the comparison isomorphism in
the new fibre. Package the component maps with `PseudoPullback.homMk` and verify the universal
property componentwise. -/

/-- A pseudo-pullback morphism is strongly cartesian exactly when both of its component
morphisms are strongly cartesian over the common base map. -/
theorem isStronglyCartesian_iff
    [X.p.IsFibered] [Y.p.IsFibered]
    (F : CartesianBasedFunctor X.p S.p) (G : CartesianBasedFunctor Y.p S.p)
    {P Q : (PseudoPullback F.toBasedFunctor G.toBasedFunctor).obj}
    (φ : P ⟶ Q) :
    (PseudoPullback F.toBasedFunctor G.toBasedFunctor).p.IsStronglyCartesian
        (PseudoPullback.baseMap φ) φ ↔
      X.p.IsStronglyCartesian
          (PseudoPullback.baseMap φ)
          (PseudoPullback.fstMap φ) ∧
        Y.p.IsStronglyCartesian
          (PseudoPullback.baseMap φ)
          (PseudoPullback.sndMap φ) := sorry
/- Proof strategy: for the forward implication, compare `φ` with the strongly cartesian lift
constructed in `projectionIsFibered`; the unique vertical comparison isomorphism projects to
vertical isomorphisms on both components. For the reverse implication, factor a competing
pseudo-pullback morphism through the two component lifts. The cartesian-preservation hypotheses
make their images in `S` strongly cartesian, so cancellation proves compatibility of the two
factor maps; `PseudoPullback.hom_ext` proves uniqueness. -/

/-- A based functor into a fibred pseudo-pullback preserves strongly cartesian arrows exactly
when both of its composites with the canonical projections do. -/
theorem preservesStronglyCartesian_iff
    [X.p.IsFibered] [Y.p.IsFibered]
    (F : CartesianBasedFunctor X.p S.p) (G : CartesianBasedFunctor Y.p S.p)
    {T : BasedCategory.{vT, uT} C}
    (K : T ⥤ᵇ PseudoPullback F.toBasedFunctor G.toBasedFunctor) :
    K.PreservesStronglyCartesian ↔
      (K ⋙ PseudoPullback.fst F.toBasedFunctor G.toBasedFunctor).PreservesStronglyCartesian ∧
        (K ⋙ PseudoPullback.snd
          F.toBasedFunctor G.toBasedFunctor).PreservesStronglyCartesian := sorry
/- Proof strategy: apply `isStronglyCartesian_iff` to every image under `K`. After expanding
based-functor composition, its two component statements are exactly the two preservation
witnesses on the right-hand side. -/

/-- The first projection from a fibred pseudo-pullback preserves strongly cartesian arrows. -/
theorem cartesianFst.preserves
    [X.p.IsFibered] [Y.p.IsFibered]
    (F : CartesianBasedFunctor X.p S.p) (G : CartesianBasedFunctor Y.p S.p) :
    (PseudoPullback.fst F.toBasedFunctor G.toBasedFunctor).PreservesStronglyCartesian := sorry
/- Proof strategy: compare a strongly cartesian pseudo-pullback arrow with the lift constructed
for `projectionIsFibered`. Uniqueness gives a vertical comparison isomorphism on the first
component; compose it with the chosen lift and use invariance under vertical isomorphism. -/

/-- The first projection from a fibred pseudo-pullback, bundled as a cartesian based functor. -/
@[stacks 0040 "first cartesian projection from an explicit pseudo-pullback"]
def cartesianFst
    [X.p.IsFibered] [Y.p.IsFibered]
    (F : CartesianBasedFunctor X.p S.p) (G : CartesianBasedFunctor Y.p S.p) :
    CartesianBasedFunctor
      (PseudoPullback F.toBasedFunctor G.toBasedFunctor).p X.p :=
  ⟨PseudoPullback.fst F.toBasedFunctor G.toBasedFunctor,
    cartesianFst.preserves F G⟩

/-- The based functor underlying the bundled first cartesian projection is the explicit
pseudo-pullback first projection. -/
@[simp]
theorem cartesianFst.toBasedFunctor
    [X.p.IsFibered] [Y.p.IsFibered]
    (F : CartesianBasedFunctor X.p S.p) (G : CartesianBasedFunctor Y.p S.p) :
    (cartesianFst F G).toBasedFunctor =
      PseudoPullback.fst F.toBasedFunctor G.toBasedFunctor := sorry

/-- Given explicit cleavages on both source projections, the first pseudo-pullback projection
preserves strongly cartesian arrows. No ambient fibredness instances are required. -/
theorem cartesianFst.ofCleavage.preserves
    (F : CartesianBasedFunctor X.p S.p) (G : CartesianBasedFunctor Y.p S.p)
    (χX : X.p.Cleavage) (χY : Y.p.Cleavage) :
    (PseudoPullback.fst F.toBasedFunctor G.toBasedFunctor).PreservesStronglyCartesian := sorry

/-- The first pseudo-pullback projection bundled from explicit source cleavages. -/
@[stacks 0040 "first cartesian pseudo-pullback projection from explicit cleavages"]
def cartesianFst.ofCleavage
    (F : CartesianBasedFunctor X.p S.p) (G : CartesianBasedFunctor Y.p S.p)
    (χX : X.p.Cleavage) (χY : Y.p.Cleavage) :
    CartesianBasedFunctor
      (PseudoPullback F.toBasedFunctor G.toBasedFunctor).p X.p :=
  ⟨PseudoPullback.fst F.toBasedFunctor G.toBasedFunctor,
    cartesianFst.ofCleavage.preserves F G χX χY⟩

/-- The based functor underlying the explicit-cleavage first cartesian projection is the first
pseudo-pullback projection. -/
@[simp]
theorem cartesianFst.ofCleavage.toBasedFunctor
    (F : CartesianBasedFunctor X.p S.p) (G : CartesianBasedFunctor Y.p S.p)
    (χX : X.p.Cleavage) (χY : Y.p.Cleavage) :
    (cartesianFst.ofCleavage F G χX χY).toBasedFunctor =
      PseudoPullback.fst F.toBasedFunctor G.toBasedFunctor := sorry

/-- Any explicit-cleavage first projection agrees with the instance-driven first projection;
the cleavage affects only the proof that the underlying projection is cartesian. -/
@[simp]
theorem cartesianFst.ofCleavage.eq
    [X.p.IsFibered] [Y.p.IsFibered]
    (F : CartesianBasedFunctor X.p S.p) (G : CartesianBasedFunctor Y.p S.p)
    (χX : X.p.Cleavage) (χY : Y.p.Cleavage) :
    cartesianFst.ofCleavage F G χX χY =
      cartesianFst F G := sorry

/-- The second projection from a fibred pseudo-pullback preserves strongly cartesian arrows. -/
theorem cartesianSnd.preserves
    [X.p.IsFibered] [Y.p.IsFibered]
    (F : CartesianBasedFunctor X.p S.p) (G : CartesianBasedFunctor Y.p S.p) :
    (PseudoPullback.snd F.toBasedFunctor G.toBasedFunctor).PreservesStronglyCartesian := sorry
/- Proof strategy: use the same comparison with the canonical lift as for
`cartesianFst.preserves`, now on the second component. -/

/-- The second projection from a fibred pseudo-pullback, bundled as a cartesian based functor. -/
@[stacks 0040 "second cartesian projection from an explicit pseudo-pullback"]
def cartesianSnd
    [X.p.IsFibered] [Y.p.IsFibered]
    (F : CartesianBasedFunctor X.p S.p) (G : CartesianBasedFunctor Y.p S.p) :
    CartesianBasedFunctor
      (PseudoPullback F.toBasedFunctor G.toBasedFunctor).p Y.p :=
  ⟨PseudoPullback.snd F.toBasedFunctor G.toBasedFunctor,
    cartesianSnd.preserves F G⟩

/-- The based functor underlying the bundled second cartesian projection is the explicit
pseudo-pullback second projection. -/
@[simp]
theorem cartesianSnd.toBasedFunctor
    [X.p.IsFibered] [Y.p.IsFibered]
    (F : CartesianBasedFunctor X.p S.p) (G : CartesianBasedFunctor Y.p S.p) :
    (cartesianSnd F G).toBasedFunctor =
      PseudoPullback.snd F.toBasedFunctor G.toBasedFunctor := sorry

/-- Given explicit cleavages on both source projections, the second pseudo-pullback projection
preserves strongly cartesian arrows. No ambient fibredness instances are required. -/
theorem cartesianSnd.ofCleavage.preserves
    (F : CartesianBasedFunctor X.p S.p) (G : CartesianBasedFunctor Y.p S.p)
    (χX : X.p.Cleavage) (χY : Y.p.Cleavage) :
    (PseudoPullback.snd F.toBasedFunctor G.toBasedFunctor).PreservesStronglyCartesian := sorry

/-- The second pseudo-pullback projection bundled from explicit source cleavages. -/
@[stacks 0040 "second cartesian pseudo-pullback projection from explicit cleavages"]
def cartesianSnd.ofCleavage
    (F : CartesianBasedFunctor X.p S.p) (G : CartesianBasedFunctor Y.p S.p)
    (χX : X.p.Cleavage) (χY : Y.p.Cleavage) :
    CartesianBasedFunctor
      (PseudoPullback F.toBasedFunctor G.toBasedFunctor).p Y.p :=
  ⟨PseudoPullback.snd F.toBasedFunctor G.toBasedFunctor,
    cartesianSnd.ofCleavage.preserves F G χX χY⟩

/-- The based functor underlying the explicit-cleavage second cartesian projection is the second
pseudo-pullback projection. -/
@[simp]
theorem cartesianSnd.ofCleavage.toBasedFunctor
    (F : CartesianBasedFunctor X.p S.p) (G : CartesianBasedFunctor Y.p S.p)
    (χX : X.p.Cleavage) (χY : Y.p.Cleavage) :
    (cartesianSnd.ofCleavage F G χX χY).toBasedFunctor =
      PseudoPullback.snd F.toBasedFunctor G.toBasedFunctor := sorry

/-- Any explicit-cleavage second projection agrees with the instance-driven second projection;
the cleavage affects only the proof that the underlying projection is cartesian. -/
@[simp]
theorem cartesianSnd.ofCleavage.eq
    [X.p.IsFibered] [Y.p.IsFibered]
    (F : CartesianBasedFunctor X.p S.p) (G : CartesianBasedFunctor Y.p S.p)
    (χX : X.p.Cleavage) (χY : Y.p.Cleavage) :
    cartesianSnd.ofCleavage F G χX χY =
      cartesianSnd F G := sorry

section Functoriality

variable {X₁ : BasedCategory.{vX₁, uX₁} C}
variable {Y₁ : BasedCategory.{vY₁, uY₁} C}
variable {S₁ : BasedCategory.{vS₁, uS₁} C}
variable {X₂ : BasedCategory.{vX₂, uX₂} C}
variable {Y₂ : BasedCategory.{vY₂, uY₂} C}
variable {S₂ : BasedCategory.{vS₂, uS₂} C}
variable {F₁ : CartesianBasedFunctor X₁.p S₁.p}
variable {G₁ : CartesianBasedFunctor Y₁.p S₁.p}
variable {F₂ : CartesianBasedFunctor X₂.p S₂.p}
variable {G₂ : CartesianBasedFunctor Y₂.p S₂.p}
variable [X₁.p.IsFibered] [Y₁.p.IsFibered]
variable [X₂.p.IsFibered] [Y₂.p.IsFibered]

/-- The explicit map of pseudo-pullbacks induced by a cartesian cospan transformation preserves
strongly cartesian arrows. Only the four endpoint projections must be fibred; the two common
targets need not be. -/
theorem cartesianMap.preservesStronglyCartesian
    (ψ : CartesianCospanTransform F₁ G₁ F₂ G₂) :
    (PseudoPullback.map ψ.toBased).PreservesStronglyCartesian := sorry

/-- Bundle the explicit componentwise map of heterogeneous pseudo-pullbacks as a cartesian
based functor. Its non-`Prop` data are exactly `BasedCategory.PseudoPullback.map ψ.toBased`. -/
@[stacks 04Y1 "cartesian map of pseudo-pullbacks"]
def cartesianMap
    (ψ : CartesianCospanTransform F₁ G₁ F₂ G₂) :
    CartesianBasedFunctor
      (PseudoPullback F₁.toBasedFunctor G₁.toBasedFunctor).p
      (PseudoPullback F₂.toBasedFunctor G₂.toBasedFunctor).p :=
  CartesianBasedFunctor.ofBasedFunctor (PseudoPullback.map ψ.toBased)
    (cartesianMap.preservesStronglyCartesian ψ)

/-- Forgetting cartesian preservation from `cartesianMap` recovers the explicit
pseudo-pullback map. -/
@[simp]
theorem cartesianMap.toBasedFunctor
    (ψ : CartesianCospanTransform F₁ G₁ F₂ G₂) :
    (cartesianMap ψ).toBasedFunctor = PseudoPullback.map ψ.toBased := sorry

end Functoriality

/- Axiom audit (mathlib 4.32): `#print axioms` for `cartesianFst`, `cartesianSnd`, and
`cartesianMap` reports `sorryAx`, but unfolding shows that it enters only through the
Prop-valued preservation fields. Their non-Prop data are definitionally `PseudoPullback.fst`,
`PseudoPullback.snd`, and `PseudoPullback.map ψ.toBased`; no functor is selected by a
placeholder. -/

end PseudoPullback
end BasedCategory

end CategoryTheory
