module

public import ReasLib.AlgebraicTopology.SimplicialObject.Copower.StdSimplex
public import ReasLib.AlgebraicTopology.SimplicialObject.InternalHom.Constant.Restriction
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Zero terms of simplicial internal-hom representations

An explicit representation of the global internal-hom presheaf restricts along constant objects
to a presheaf represented by its degree-zero term.  This statement is independent of skeletons;
the chosen `internalHom` is only a specialization of the explicit `RepresentableBy` API.
-/

@[expose] public section

open CategoryTheory Opposite
open scoped Simplicial

noncomputable section

universe w v u

namespace CategoryTheory.SimplicialObject.internalHom.zero

variable {C : Type u} [Category.{v} C]
variable (U : SSet.{w}) (V : SimplicialObject C)
variable [HasCopowers U C]
variable {M : SimplicialObject C}

/-- The Hom equivalence exhibiting the zero term of an explicit internal-hom representation as
the representation of the constant-object restriction. -/
@[stacks 018V "zero term of an explicit internal-hom representation"]
noncomputable def homEquiv
    (R : (presheaf U V).RepresentableBy M) (X : C) :
    (X ⟶ M.obj (op (SimplexCategory.mk 0))) ≃
      (constRestriction U V).obj (op X) :=
  (copower.stdSimplex.homEquiv.{v} 0 X M).symm.trans
    (R.homEquiv.trans
      (((presheaf U V).mapIso (copower.zeroSimplex.iso.{v} X).op).toEquiv.symm))

/-- The zero-term representing equivalence is natural in the constant object. -/
@[stacks 018V "zero-term representation naturality"]
theorem homEquiv.comp
    (R : (presheaf U V).RepresentableBy M) {X Y : C} (f : X ⟶ Y)
    (g : Y ⟶ M.obj (op (SimplexCategory.mk 0))) :
    homEquiv U V R X (f ≫ g) =
      (constRestriction U V).map f.op (homEquiv U V R Y g) := sorry

/-- An explicit representation of the global mapping presheaf represents its constant-object
restriction by its zero term. -/
@[stacks 018V "explicit zero-term representation"]
noncomputable def representableBy
    (R : (presheaf U V).RepresentableBy M) :
    (constRestriction U V).RepresentableBy
      (M.obj (op (SimplexCategory.mk 0))) where
  homEquiv {X} := homEquiv U V R X
  homEquiv_comp := homEquiv.comp U V R

/-- The zero term of the chosen internal mapping object represents the constant-object
restriction. -/
@[stacks 018V "chosen zero-term representation"]
noncomputable def representable
    [Functor.IsRepresentable (presheaf U V)] :
    (constRestriction U V).RepresentableBy
      ((internalHom U V).obj (op (SimplexCategory.mk 0))) :=
  representableBy U V (presheaf U V).representableBy

end CategoryTheory.SimplicialObject.internalHom.zero
