/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.OpenImmersion
import ReasLib.Algebra.Module.Torsion.BaseChange
public import ReasLib.RingTheory.Kaehler.NoetherDifferent

@[expose] public section

open AlgebraicGeometry

universe u v

namespace KaehlerDifferential

/-- The annihilator of the diagonal ideal is preserved by extension along an affine open
immersion whose source algebra is of finite type. -/
theorem annihilator_eq_map_of_isOpenImmersion
    {A : Type u} {B' B : Type v}
    [CommRing A] [CommRing B'] [CommRing B] [Algebra A B'] [Algebra A B]
    [Algebra.FiniteType A B'] (f : B' →ₐ[A] B)
    [IsOpenImmersion (Spec.map (CommRingCat.ofHom f.toRingHom))] :
    (ideal A B).annihilator =
      Ideal.map (Algebra.TensorProduct.map f f).toRingHom (ideal A B').annihilator := sorry

/-- The Noether different is preserved by extension along an affine open immersion whose
source algebra is of finite type. -/
theorem noetherDifferent_eq_map_of_isOpenImmersion
    {A : Type u} {B' B : Type v}
    [CommRing A] [CommRing B'] [CommRing B] [Algebra A B'] [Algebra A B]
    [Algebra.FiniteType A B'] (f : B' →ₐ[A] B)
    [IsOpenImmersion (Spec.map (CommRingCat.ofHom f.toRingHom))] :
    noetherDifferent A B = Ideal.map f.toRingHom (noetherDifferent A B') := sorry

end KaehlerDifferential
