module

public import ReasLib.AlgebraicGeometry.Scheme.QuasiCoherentAlgebra.FiniteTypeGeneration
public import ReasLib.AlgebraicGeometry.Scheme.QuasiCoherentAlgebra.Finite
public import ReasLib.AlgebraicGeometry.Scheme.QuasiCoherentAlgebra.Sections
public import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic

/-!
# Integral quasi-coherent algebra sheaves

This file defines integrality of quasi-coherent algebra sheaves and states their approximation by
finite quasi-coherent algebra sheaves.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.QcAlgebraUnder

/-- A quasi-coherent algebra sheaf is integral if its structure map on every affine open is an
integral ring homomorphism. -/
def IsIntegral {S : Scheme.{u}} (A : S.QcAlgebraUnder) : Prop :=
  ∀ (U : S.Opens), IsAffineOpen U → (qcAlgebraStructureMap A U).hom.IsIntegral

/-- The subalgebras of a quasi-coherent algebra sheaf whose carrier algebras are
quasi-coherent and finite over the structure sheaf. -/
def finiteQuasiCoherentSubalgebras {S : Scheme.{u}} (A : S.QcAlgebraUnder) :
    Set (Subobject A.obj) :=
  { B | qcAlgebraUnderProperty S (B : Under (schemeCommRingSheaf S)) ∧
      finiteProperty S (B : Under (schemeCommRingSheaf S)) }

/-- A subalgebra belongs to `finiteQuasiCoherentSubalgebras A` exactly when its carrier algebra
is quasi-coherent and finite over the structure sheaf. -/
@[simp] theorem mem_finiteQuasiCoherentSubalgebras
    {S : Scheme.{u}} (A : S.QcAlgebraUnder) (B : Subobject A.obj) :
    B ∈ finiteQuasiCoherentSubalgebras A ↔
      qcAlgebraUnderProperty S (B : Under (schemeCommRingSheaf S)) ∧
        finiteProperty S (B : Under (schemeCommRingSheaf S)) :=
  Iff.rfl

namespace IsIntegral

/-- For an integral quasi-coherent algebra sheaf, a quasi-coherent subalgebra is of finite type
exactly when it is finite over the structure sheaf. -/
theorem finiteTypeQuasiCoherentSubalgebras_eq_finiteQuasiCoherentSubalgebras
    {S : Scheme.{u}} [CompactSpace S] [QuasiSeparatedSpace S]
    {A : S.QcAlgebraUnder} (hA : A.IsIntegral) :
    finiteTypeQuasiCoherentSubalgebras A = finiteQuasiCoherentSubalgebras A := sorry

end IsIntegral

/-- On a quasi-compact quasi-separated scheme, the finite quasi-coherent subalgebras of an
integral quasi-coherent algebra sheaf are directed by inclusion and have supremum the whole
algebra. -/
theorem finiteQuasiCoherentSubalgebras_isDirectedColimit_of_isIntegral
    {S : Scheme.{u}} [CompactSpace S] [QuasiSeparatedSpace S]
    (A : S.QcAlgebraUnder) (hA : A.IsIntegral) :
    DirectedOn (· ≤ ·) (finiteQuasiCoherentSubalgebras A) ∧
      IsLUB (finiteQuasiCoherentSubalgebras A) (⊤ : Subobject A.obj) := sorry

/-- On a quasi-compact quasi-separated scheme, an integral quasi-coherent algebra sheaf is a
filtered colimit of algebra sheaves that are both finite and finitely presentable. -/
theorem finiteFinitelyPresentable_ind_of_isIntegral
    {S : Scheme.{u}} [CompactSpace S] [QuasiSeparatedSpace S]
    (A : S.QcAlgebraUnder) (hA : A.IsIntegral) :
    ObjectProperty.ind.{u}
      (fun B : Under (schemeCommRingSheaf S) ↦
        finiteProperty S B ∧ finitelyPresentableProperty S B) A.obj := sorry

end AlgebraicGeometry.Scheme.QcAlgebraUnder

end
