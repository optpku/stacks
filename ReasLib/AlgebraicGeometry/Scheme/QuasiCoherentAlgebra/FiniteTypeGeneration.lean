/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.QuasiCoherentAlgebra.FinitePresentation

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.QcAlgebraUnder

/-- An algebra sheaf is of finite type if it is the target of an epimorphism from a finitely
presentable algebra sheaf. -/
def finiteTypeProperty (S : Scheme.{u}) :
    ObjectProperty (Under (schemeCommRingSheaf S)) :=
  fun B ↦ ∃ P : Under (schemeCommRingSheaf S),
    IsFinitelyPresentable.{u} P ∧ ∃ π : P ⟶ B, Epi π

/-- The subalgebras of a quasi-coherent algebra sheaf whose carrier algebras are
quasi-coherent and of finite type. -/
def finiteTypeQuasiCoherentSubalgebras {S : Scheme.{u}} (A : S.QcAlgebraUnder) :
    Set (Subobject A.obj) :=
  { B | qcAlgebraUnderProperty S (B : Under (schemeCommRingSheaf S)) ∧
      finiteTypeProperty S (B : Under (schemeCommRingSheaf S)) }

/-- A subalgebra belongs to `finiteTypeQuasiCoherentSubalgebras A` exactly when its carrier
algebra is quasi-coherent and of finite type. -/
@[simp] theorem mem_finiteTypeQuasiCoherentSubalgebras
    {S : Scheme.{u}} (A : S.QcAlgebraUnder) (B : Subobject A.obj) :
    B ∈ finiteTypeQuasiCoherentSubalgebras A ↔
      qcAlgebraUnderProperty S (B : Under (schemeCommRingSheaf S)) ∧
        finiteTypeProperty S (B : Under (schemeCommRingSheaf S)) :=
  Iff.rfl

/-- On a quasi-compact quasi-separated scheme, the finite-type quasi-coherent subalgebras of
a quasi-coherent algebra sheaf are directed by inclusion and have supremum the whole algebra. -/
theorem finiteTypeQuasiCoherentSubalgebras_isDirectedColimit
    {S : Scheme.{u}} [CompactSpace S] [QuasiSeparatedSpace S]
    (A : S.QcAlgebraUnder) :
    DirectedOn (· ≤ ·) (finiteTypeQuasiCoherentSubalgebras A) ∧
      IsLUB (finiteTypeQuasiCoherentSubalgebras A) (⊤ : Subobject A.obj) := sorry

end AlgebraicGeometry.Scheme.QcAlgebraUnder

end
