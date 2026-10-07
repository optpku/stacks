module

public import Mathlib.Algebra.Category.Ring.Colimits
public import ReasLib.AlgebraicGeometry.Scheme.Limit.DirectedAffine
public import stacks_project.Chap61.«61_5_2_6_Diagram»

/-!
# Affine w-local schemes as directed limits

The ring `A_w` is the filtered colimit of the finite-stage algebras `A_E`.
The associated affine scheme `X_w` is the explicit directed limit of the
inverse system `X_E`, and the closed subscheme `Z` is the explicit directed
limit of the inverse system `Z_E`, with closed immersion `Z ⟶ X_w`.
-/

@[expose] public section

open CategoryTheory Limits Opposite AlgebraicGeometry CommRingCat
open Algebra.WLocalHull

noncomputable section

universe u

namespace AlgebraicGeometry.WLocal.Construction

variable (A : Type u) [CommRing A]

/-- The w-local affine ring `A_w`, as the filtered colimit of the finite-stage
algebras `A_E`. -/
def ring : CommRingCat.{u} :=
  colimit (ringFunctor A)

/-- The cocone map `A_E ⟶ A_w` from a finite-stage algebra into the colimit. -/
def ring_ι (E : Finset A) : (ringFunctor A).obj E ⟶ ring A :=
  colimit.ι (ringFunctor A) E

/-- The explicit affine limit cone on the inverse system `X_E`. -/
def schemeCone : Cone (schemeFunctor A) :=
  Scheme.Limit.DirectedAffine.cone (schemeFunctor A)

/-- The affine scheme `X_w`, as the vertex of the explicit directed limit of
the inverse system `X_E`. -/
def scheme : Scheme.{u} :=
  (schemeCone A).pt

/-- The explicit affine cone on `X_E` is a limit cone, so `X_w = lim_E X_E`. -/
def isLimit_schemeCone : IsLimit (schemeCone A) :=
  Scheme.Limit.DirectedAffine.cone_isLimit (schemeFunctor A)

/-- The inverse system of finite-stage schemes `X_E` has a limit. -/
instance hasLimit_schemeFunctor : HasLimit (schemeFunctor A) :=
  HasLimit.mk ⟨schemeCone A, isLimit_schemeCone A⟩

/-- The scheme `X_w` is affine. -/
instance isAffine_scheme : IsAffine (scheme A) :=
  inferInstanceAs (IsAffine (Scheme.Limit.DirectedAffine.scheme (schemeFunctor A)))

/-- Projection from `X_w` onto a finite-stage scheme `X_E`. -/
def scheme_π (E : Finset A) : scheme A ⟶ spectrum A E :=
  (schemeCone A).π.app (OrderDual.toDual E)

/-- The closed-stage colimit ring `colim_E Γ(Z_E)`. -/
def closedRing : CommRingCat.{u} :=
  colimit (closedStageRingFunctor A)

/-- The cocone map `Γ(Z_E) ⟶ colim Γ(Z_F)` from a finite-stage closed algebra. -/
def closedRing_ι (E : Finset A) :
    (closedStageRingFunctor A).obj E ⟶ closedRing A :=
  colimit.ι (closedStageRingFunctor A) E

/-- The explicit affine limit cone on the inverse system `Z_E`. -/
def closedCone : Cone (closedFunctor A) :=
  Scheme.Limit.DirectedAffine.cone (closedFunctor A)

/-- The closed subscheme `Z`, as the vertex of the explicit directed limit of
the inverse system `Z_E`. -/
def closedSubscheme : Scheme.{u} :=
  (closedCone A).pt

/-- The explicit affine cone on `Z_E` is a limit cone, so `Z = lim_E Z_E`. -/
def isLimit_closedCone : IsLimit (closedCone A) :=
  Scheme.Limit.DirectedAffine.cone_isLimit (closedFunctor A)

/-- The inverse system of finite-stage closed subschemes `Z_E` has a limit. -/
instance hasLimit_closedFunctor : HasLimit (closedFunctor A) :=
  HasLimit.mk ⟨closedCone A, isLimit_closedCone A⟩

/-- The scheme `Z` is affine. -/
instance isAffine_closedSubscheme : IsAffine (closedSubscheme A) :=
  inferInstanceAs (IsAffine (Scheme.Limit.DirectedAffine.scheme (closedFunctor A)))

/-- Projection from `Z` onto a finite-stage closed subscheme `Z_E`. -/
def closed_π (E : Finset A) :
    closedSubscheme A ⟶ Spec (of (closedStage A E)) :=
  (closedCone A).π.app (OrderDual.toDual E)

/-- The closed immersion `Z ⟶ X_w` induced by the compatible family of
finite-stage closed immersions `Z_E ⟶ X_E`. -/
def closedι : closedSubscheme A ⟶ scheme A :=
  (isLimit_schemeCone A).lift ((Cone.postcompose (closedιNatTrans A)).obj (closedCone A))

/-- The inclusion `Z ⟶ X_w` is a closed immersion. -/
instance isClosedImmersion_closedι : IsClosedImmersion (closedι A) := sorry

/-- The projections `X_w ⟶ X_E` intertwine `closedι` with the finite-stage
closed immersions `Z_E ⟶ X_E`. -/
theorem closedι_comp_π (E : Finset A) :
    closedι A ≫ scheme_π A E = closed_π A E ≫ closedHom A E := sorry

end AlgebraicGeometry.WLocal.Construction
