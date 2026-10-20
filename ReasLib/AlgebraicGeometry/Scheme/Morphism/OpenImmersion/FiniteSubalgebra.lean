/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.OpenImmersion.BasicOpen
public import ReasLib.RingTheory.QuasiFinite.FiniteType

@[expose] public section

open AlgebraicGeometry

universe u v

namespace AlgebraicGeometry.IsOpenImmersion

/-- Two finite algebras mapping to a finite-type quasi-finite algebra through open immersions
of spectra admit a common finite subalgebra through which both maps factor and whose spectrum
map is an open immersion. -/
theorem exists_common_finiteSubalgebra
    {A : Type u} {B B' B'' : Type v}
    [CommRing A] [CommRing B] [CommRing B'] [CommRing B'']
    [Algebra A B] [Algebra A B'] [Algebra A B'']
    (h_quasiFinite : Algebra.FiniteType.QuasiFinite A B)
    [Module.Finite A B'] [Module.Finite A B'']
    (f' : B' →ₐ[A] B) (f'' : B'' →ₐ[A] B)
    (h_open' : IsOpenImmersion (Spec.map (CommRingCat.ofHom f'.toRingHom)))
    (h_open'' : IsOpenImmersion (Spec.map (CommRingCat.ofHom f''.toRingHom))) :
    ∃ C : Subalgebra A B,
      Module.Finite A C ∧
        IsOpenImmersion (Spec.map (CommRingCat.ofHom C.val.toRingHom)) ∧
          f'.range ⊔ f''.range ≤ C := sorry

end AlgebraicGeometry.IsOpenImmersion
