module

public import Mathlib.Algebra.Homology.ShortComplex.Exact
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Stalk
public import ReasLib.AlgebraicGeometry.Scheme.Module.Quasicoherent

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.QCoh

/-- Taking the stalk at a point of a scheme is a functor from quasicoherent modules to
modules over the stalk of the structure sheaf. -/
noncomputable def stalkFunctor (X : Scheme.{u}) (x : X) :
    Scheme.QCoh X ⥤ ModuleCat (X.ringCatSheaf.presheaf.stalk x) :=
  Scheme.QCoh.inclusion X ⋙ SheafOfModules.stalkFunctor X.ringCatSheaf x

/-- The short complex of stalks of a short complex of quasicoherent modules. -/
noncomputable def stalkShortComplex {X : Scheme.{u}}
    (S : ShortComplex (Scheme.QCoh X)) (x : X) :
    ShortComplex (ModuleCat (X.ringCatSheaf.presheaf.stalk x)) :=
  let T := S.map (Scheme.QCoh.inclusion X)
  -- Use the sheaf-module category instance for the second map.
  let T' : ShortComplex (SheafOfModules.{u} X.ringCatSheaf) := T
  T'.map (SheafOfModules.stalkFunctor X.ringCatSheaf x)

/-- A short complex of quasicoherent modules is stalkwise split exact when it is short exact
and its short complex of stalks admits a splitting at every point. -/
def IsStalkwiseSplitExact {X : Scheme.{u}} (S : ShortComplex (Scheme.QCoh X)) : Prop :=
  S.ShortExact ∧ ∀ x : X, Nonempty (stalkShortComplex S x).Splitting

end AlgebraicGeometry.Scheme.QCoh
