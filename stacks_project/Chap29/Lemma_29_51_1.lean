module

import ReasLib.AlgebraicGeometry.Scheme.Morphism.QuasiFinite.GenericFiber
import StacksCheckRecall

open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

/- Lemma 29.51.1 (1): for a locally finite type morphism `f : X ⟶ Y` and a generic point `η`
of an irreducible component of `Y`, the fiber over `η` is finite if and only if it is covered by
finitely many affine opens over one affine neighborhood of `η` on which the restrictions of `f`
are finite. -/
@[stacks 02NW] #check
  (AlgebraicGeometry.Scheme.Hom.tfae_finiteFiber_finiteAffineCover :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFiniteType f] {η : Y},
      η ∈ genericPoints Y →
        List.TFAE
          [ ({x : X | f x = η} : Set X).Finite
          , (∃ (n : ℕ) (U : Fin n → X.Opens) (V : Y.Opens)
                (_ : IsAffineOpen V) (_ : ∀ i, IsAffineOpen (U i)) (_ : η ∈ V)
                (hUV : ∀ i, U i ≤ f ⁻¹ᵁ V)
                (_ : ∀ x : X, f x = η → ∃ i : Fin n, x ∈ U i),
              ∀ i, IsFinite (f.resLE V (U i) (hUV i)))
          ])

/- Lemma 29.51.1 (2): if the locally finite type morphism `f : X ⟶ Y` is quasi-separated, then
the finite-fiber condition over a generic point `η` of an irreducible component of `Y`, the finite
affine-open-cover condition, and the existence of one affine open `U` over an affine neighborhood
of `η` with finite restriction are equivalent. -/
@[stacks 02NW] #check
  (AlgebraicGeometry.Scheme.Hom.tfae_finiteFiber_finiteAffineOpen_of_quasiSeparated :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFiniteType f] [QuasiSeparated f] {η : Y},
      η ∈ genericPoints Y →
        List.TFAE
          [ ({x : X | f x = η} : Set X).Finite
          , (∃ (n : ℕ) (U : Fin n → X.Opens) (V : Y.Opens)
                (_ : IsAffineOpen V) (_ : ∀ i, IsAffineOpen (U i)) (_ : η ∈ V)
                (hUV : ∀ i, U i ≤ f ⁻¹ᵁ V)
                (_ : ∀ x : X, f x = η → ∃ i : Fin n, x ∈ U i),
              ∀ i, IsFinite (f.resLE V (U i) (hUV i)))
          , (∃ (U : X.Opens) (V : Y.Opens)
                (_ : IsAffineOpen U) (_ : IsAffineOpen V) (_ : η ∈ V)
                (hUV : U ≤ f ⁻¹ᵁ V) (_ : ∀ x : X, f x = η → x ∈ U),
              IsFinite (f.resLE V U hUV))
          ])

/- Lemma 29.51.1 (3): if the locally finite type morphism `f : X ⟶ Y` is quasi-compact and
quasi-separated, then the finite-fiber condition over a generic point `η`, the finite affine cover
condition, the one-affine-open finite restriction condition, and finite restriction over some
affine neighborhood of `η` in the target are equivalent. -/
@[stacks 02NW] #check
  (AlgebraicGeometry.Scheme.Hom.tfae_finiteFiber_finiteRestriction_of_quasiCompact_quasiSeparated :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFiniteType f] [QuasiCompact f]
      [QuasiSeparated f] {η : Y},
      η ∈ genericPoints Y →
        List.TFAE
          [ ({x : X | f x = η} : Set X).Finite
          , (∃ (n : ℕ) (U : Fin n → X.Opens) (V : Y.Opens)
                (_ : IsAffineOpen V) (_ : ∀ i, IsAffineOpen (U i)) (_ : η ∈ V)
                (hUV : ∀ i, U i ≤ f ⁻¹ᵁ V)
                (_ : ∀ x : X, f x = η → ∃ i : Fin n, x ∈ U i),
              ∀ i, IsFinite (f.resLE V (U i) (hUV i)))
          , (∃ (U : X.Opens) (V : Y.Opens)
                (_ : IsAffineOpen U) (_ : IsAffineOpen V) (_ : η ∈ V)
                (hUV : U ≤ f ⁻¹ᵁ V) (_ : ∀ x : X, f x = η → x ∈ U),
              IsFinite (f.resLE V U hUV))
          , (∃ (V : Y.Opens) (_ : IsAffineOpen V) (_ : η ∈ V), IsFinite (f ∣_ V))
          ])
