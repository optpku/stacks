module

public import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
public import ReasLib.AlgebraicGeometry.GroupoidScheme.IrreducibleComponent
public import ReasLib.AlgebraicGeometry.Scheme.FieldExtension.Stalk.Local
public import ReasLib.AlgebraicGeometry.Scheme.OverField.Local

/-!
# Stalks of groupoid schemes over fields

This module records the uniqueness of minimal primes in stalks of the arrow scheme of a
groupoid scheme whose object scheme is a field spectrum.
-/

@[expose] public section

open CategoryTheory TopologicalSpace AlgebraicGeometry.Scheme

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidScheme

/-- Every local ring of the arrow scheme of a groupoid scheme over a field has a unique minimal
prime ideal. -/
theorem existsUniqueMinimalPrime_stalk {S : Scheme.{u}} (G : GroupoidScheme S)
    {k : Type u} [Field k] (uIso : G.U.left ≅ Spec (CommRingCat.of k))
    (r : G.R.left) :
    let R := G.R.left
    ∃! p : Ideal (R.presheaf.stalk r),
      p ∈ minimalPrimes (R.presheaf.stalk r) := by
  sorry

end AlgebraicGeometry.GroupoidScheme
