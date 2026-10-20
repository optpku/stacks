module

public import ReasLib.RingTheory.Ideal.Map
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.TensorProduct.Quotient
public import Mathlib.Order.Hom.BoundedLattice
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Flat extension of ideals

This leaf owns the finite-intersection API for ideal extension along a flat
module or flat algebra.  The bundled `InfTopHom` is the reusable object for
later finite-infimum arguments; the Chapter 10 file is only a tagged recall.
-/

@[expose] public section

open scoped TensorProduct

universe u v

namespace Ideal

section Module

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M] [Module.Flat R M]

/-- Lemma 10.39.2 (module form): a flat module preserves the intersection
of the two ideal multiples of its top submodule. -/
@[stacks 0BBY "flat module ideal intersection"]
theorem smul_top_inf_smul_top_eq_inf_smul_top_of_flat (I J : Ideal R) :
    I • (⊤ : Submodule R M) ⊓ J • (⊤ : Submodule R M) =
      (I ⊓ J) • (⊤ : Submodule R M) := sorry
/- Proof strategy: identify the product of the two quotient-tensor maps with
the tensor of `R → R ⧸ I × R ⧸ J`, use flatness to compute its kernel, and
rewrite the resulting image as `(I ⊓ J) • ⊤`. -/

end Module

section Algebra

variable {R : Type u} [CommRing R]
variable {S : Type v} [CommRing S] [Algebra R S] [Module.Flat R S]

/-- Lemma 10.39.2 (algebra form): a flat algebra map preserves binary
intersections of ideals. -/
@[stacks 0BBY "flat algebra ideal intersection"]
theorem map_inf_of_flat (I J : Ideal R) :
    Ideal.map (algebraMap R S) (I ⊓ J) =
      Ideal.map (algebraMap R S) I ⊓ Ideal.map (algebraMap R S) J := sorry
/- Proof strategy: specialize the flat-module intersection theorem to `S`
and rewrite every ideal multiple of `⊤` with `Ideal.smul_top_eq_map`. -/

/-- Lemma 10.39.2 owner: extension of ideals along a flat algebra map,
bundled as the finite-infimum and top-preserving homomorphism used downstream. -/
@[stacks 0BBY "flat ideal extension InfTopHom"]
def mapInfTopHom : InfTopHom (Ideal R) (Ideal S) where
  toFun := Ideal.map (algebraMap R S)
  map_inf' := map_inf_of_flat
  map_top' := map_top _

/-- The bundled flat ideal-extension map evaluates to the ordinary ideal map. -/
@[simp]
theorem mapInfTopHom_apply (I : Ideal R) :
    mapInfTopHom I = Ideal.map (algebraMap R S) I := sorry
/- Proof strategy: unfold `mapInfTopHom`; its `toFun` field is definitionally
the ordinary extension map. -/

end Algebra

end Ideal
