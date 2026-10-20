/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.Embedding.Monoidal
public import Mathlib.Algebra.Homology.Bifunctor
import Mathlib.Tactic.CrossRefAttribute

/-!
@stack 07MB

# Extension by zero and heterogeneous bifunctors

An additive embedding of complex shapes commutes with totalizing a curried bifunctor.  The
comparison in this file is heterogeneous: the two input complexes and the output complex may
belong to different categories.  This is the extension-by-zero bridge needed for tensor products
of modules in different universes, where no same-universe monoidal structure is available.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe w w' uA vA uB vB uD vD

namespace ComplexShape.Embedding

variable {I : Type w} {I' : Type w'} [AddMonoid I] [AddMonoid I']
variable {c : ComplexShape I} {c' : ComplexShape I'}
variable {A : Type uA} [Category.{vA} A] [Preadditive A] [HasZeroObject A]
variable {B : Type uB} [Category.{vB} B] [Preadditive B] [HasZeroObject B]
variable {D : Type uD} [Category.{vD} D] [Preadditive D] [HasZeroObject D]
variable (e : c.Embedding c')
variable [DecidableEq I] [DecidableEq I'] [c.TensorSigns] [c'.TensorSigns]
variable (T : A ⥤ B ⥤ D) [T.PreservesZeroMorphisms]
variable [∀ X, (T.obj X).PreservesZeroMorphisms]
variable (K : HomologicalComplex A c) (L : HomologicalComplex B c)
variable [HomologicalComplex.HasMapBifunctor K L T c]
variable [HomologicalComplex.HasMapBifunctor (K.extend e) (L.extend e) T c']

/-- The degreewise comparison from the total of two extended complexes to the extension of their
heterogeneous total.  Each nonzero summand is transported back to its source degrees before it is
inserted into the original total complex. -/
@[stacks 07MB "degreewise heterogeneous extension comparison"]
noncomputable def extendBifunctorHomF [e.IsAdditive] (n' : I') :
    (HomologicalComplex.mapBifunctor (K.extend e) (L.extend e) T c').X n' ⟶
      ((HomologicalComplex.mapBifunctor K L T c).extend e).X n' :=
  HomologicalComplex.mapBifunctorDesc (K₁ := K.extend e) (K₂ := L.extend e)
      (F := T) (c := c') (fun i' j' hij ↦
    match hi : e.r i', hj : e.r j' with
    | some i, some j =>
        (T.map (K.extendXIso e (e.f_eq_of_r_eq_some hi)).hom).app ((L.extend e).X j') ≫
          (T.obj (K.X i)).map (L.extendXIso e (e.f_eq_of_r_eq_some hj)).hom ≫
            HomologicalComplex.ιMapBifunctor K L T c i j (i + j) rfl ≫
              ((HomologicalComplex.mapBifunctor K L T c).extendXIso e
                ((e.addMonoidHom.map_add i j).trans
              ((congrArg₂ (· + ·) (e.f_eq_of_r_eq_some hi)
                    (e.f_eq_of_r_eq_some hj)).trans hij))).inv
    | _, _ => 0)

/-- The degreewise heterogeneous extension comparison commutes with the differentials. -/
@[stacks 07MB "chain compatibility of the heterogeneous extension comparison"]
theorem extendBifunctorHomF_comm [e.PreservesTensorSigns]
    (i' j' : I') (hij : c'.Rel i' j') :
    e.extendBifunctorHomF (K := K) (L := L) T i' ≫
        ((HomologicalComplex.mapBifunctor K L T c).extend e).d i' j' =
      (HomologicalComplex.mapBifunctor (K.extend e) (L.extend e) T c').d i' j' ≫
        e.extendBifunctorHomF (K := K) (L := L) T j' := sorry

/-- Extension by zero commutes with totalizing a heterogeneous bifunctor. -/
@[stacks 07MB "heterogeneous bifunctor comparison for extension by zero"]
noncomputable def extendBifunctorHom [e.PreservesTensorSigns] :
    HomologicalComplex.mapBifunctor (K.extend e) (L.extend e) T c' ⟶
      (HomologicalComplex.mapBifunctor K L T c).extend e :=
  HomologicalComplex.Hom.mk (e.extendBifunctorHomF (K := K) (L := L) T)
    (e.extendBifunctorHomF_comm (K := K) (L := L) T)

/-- The degree component of the heterogeneous extension comparison is its explicit summand
descent. -/
@[simp, stacks 07MB "degree component of the heterogeneous extension comparison"]
theorem extendBifunctorHom_f [e.PreservesTensorSigns] (n' : I') :
    (e.extendBifunctorHom (K := K) (L := L) T).f n' =
      e.extendBifunctorHomF (K := K) (L := L) T n' := sorry

end ComplexShape.Embedding

end
