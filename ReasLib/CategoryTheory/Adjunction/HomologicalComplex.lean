module

public import Mathlib.Algebra.Homology.Additive
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import Mathlib.CategoryTheory.Adjunction.Additive
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Exact Adjunctions on Homological Complexes

An exact left adjoint is additive, and hence so is its right adjoint.  This
leaf packages the induced map on homological complexes so that downstream
statements retain only the mathematical hypotheses `adj` and `h_exact` rather
than repeatedly creating proof-local additive instances.
-/

open ComplexShape
open CategoryTheory.Limits

universe uA uB vA vB uI

namespace CategoryTheory.Adjunction.Exact

variable {A : Type uA} {B : Type uB} {ι : Type uI}
  [Category.{vA} A] [Category.{vB} B]
  [Preadditive A] [Preadditive B]
  [HasZeroObject A] [HasZeroObject B] [HasBinaryBiproducts B]
  {u : A ⥤ B} {v : B ⥤ A}

/-- Stacks 08BJ: an exact left adjoint induces the map on homological complexes
of its right adjoint.  The additive structures are derived internally from
the supplied exactness and adjunction, not required as ambient inputs. -/
@[stacks 08BJ]
def mapHomologicalComplex
    (adj : v ⊣ u) (h_exact : exactFunctor B A v) (c : ComplexShape ι) :
    HomologicalComplex A c ⥤ HomologicalComplex B c :=
  -- Local instance justification (proof-local temporary data): `h_exact` is
  -- intentionally explicit, and Mathlib's additive consequences are needed
  -- only while constructing this concrete complex functor; globalizing them
  -- would create competing additive instances for the same adjunction.
  letI : v.Additive := (exactFunctor_le_additiveFunctor B A) v h_exact
  letI : u.Additive := adj.right_adjoint_additive
  u.mapHomologicalComplex c

/-- With an ambient additive instance on the right adjoint, the exact-adjunction complex map is
the standard Mathlib map on homological complexes. -/
theorem mapHomologicalComplex_eq
    (adj : v ⊣ u) (h_exact : exactFunctor B A v) (c : ComplexShape ι)
    [u.Additive] :
    mapHomologicalComplex adj h_exact c = u.mapHomologicalComplex c := sorry

/-- The exact-left-adjoint complex map applies the underlying right adjoint in
each degree. -/
@[simp]
theorem mapHomologicalComplex_obj_X
    (adj : v ⊣ u) (h_exact : exactFunctor B A v) (c : ComplexShape ι)
    (K : HomologicalComplex A c) (i : ι) :
    ((mapHomologicalComplex adj h_exact c).obj K).X i = u.obj (K.X i) := sorry

/-- The differential of the exact-left-adjoint complex map is the image of
the original differential under the underlying right adjoint. -/
@[simp]
theorem mapHomologicalComplex_obj_d
    (adj : v ⊣ u) (h_exact : exactFunctor B A v) (c : ComplexShape ι)
    (K : HomologicalComplex A c) (i j : ι) :
    ((mapHomologicalComplex adj h_exact c).obj K).d i j = u.map (K.d i j) := sorry

/-- The exact-left-adjoint complex map applies the underlying right adjoint to
each component of a morphism of complexes. -/
@[simp]
theorem mapHomologicalComplex_map_f
    (adj : v ⊣ u) (h_exact : exactFunctor B A v) (c : ComplexShape ι)
    {K L : HomologicalComplex A c} (f : K ⟶ L) (i : ι) :
    ((mapHomologicalComplex adj h_exact c).map f).f i = u.map (f.f i) := sorry

end CategoryTheory.Adjunction.Exact
