module

public import ReasLib.AlgebraicGeometry.Scheme.Distance
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType.Noetherian
public import ReasLib.AlgebraicGeometry.Scheme.Variety.AffinePresentation

@[expose] public section

open Set TopologicalSpace
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

/-- In affine `n`-space over a field, the distance from `y` to a closed point `z`
to which `y` specializes is the dimension of `closure {y}`. -/
theorem distanceToClosedPoint_of_specializes
    {k : Type u} [Field k] (n : ℕ) {y z : AffineSpaceOverField k n}
    (hz : IsClosed ({z} : Set (AffineSpaceOverField k n))) (hyz : y ⤳ z) :
    (@distanceTo (AffineSpaceOverField k n)
        (Hom.FiniteType.isNoetherian (affineSpaceOverFieldHom k n))
        (⟨({z} : Set (AffineSpaceOverField k n)), hz⟩ : Closeds (AffineSpaceOverField k n)) y :
      WithBot ℕ∞) =
      topologicalKrullDim (closure ({y} : Set (AffineSpaceOverField k n))) := sorry

/-- In affine `n`-space over a field, the distance from `y` to a closed point `z`
to which `y` does not specialize is one more than the dimension of `closure {y}`. -/
theorem distanceToClosedPoint_of_not_specializes
    {k : Type u} [Field k] (n : ℕ) {y z : AffineSpaceOverField k n}
    (hz : IsClosed ({z} : Set (AffineSpaceOverField k n))) (hyz : ¬y ⤳ z) :
    (@distanceTo (AffineSpaceOverField k n)
        (Hom.FiniteType.isNoetherian (affineSpaceOverFieldHom k n))
        (⟨({z} : Set (AffineSpaceOverField k n)), hz⟩ : Closeds (AffineSpaceOverField k n)) y :
      WithBot ℕ∞) =
      topologicalKrullDim (closure ({y} : Set (AffineSpaceOverField k n))) + 1 := sorry

/-- If the closure of `y` is contained in an irreducible closed subset `Z` of affine
space over a field, then the distance from `y` to `Z` is zero. -/
theorem distanceToSubvariety_of_closure_subset
    {k : Type u} [Field k] (n : ℕ) (Z : Closeds (AffineSpaceOverField k n))
    (hZ : IsIrreducible (Z : Set (AffineSpaceOverField k n))) (y : AffineSpaceOverField k n)
    (hWZ : Closeds.closure ({y} : Set (AffineSpaceOverField k n)) ≤ Z) :
    @distanceTo (AffineSpaceOverField k n)
      (Hom.FiniteType.isNoetherian (affineSpaceOverFieldHom k n)) Z y = 0 := sorry

/-- If an irreducible closed subset `Z` of affine space over a field is contained in
`closure {y}`, then the distance is `dim (closure {y}) - dim Z`. -/
theorem distanceToSubvariety_of_subset_closure
    {k : Type u} [Field k] (n : ℕ) (Z : Closeds (AffineSpaceOverField k n))
    (hZ : IsIrreducible (Z : Set (AffineSpaceOverField k n))) (y : AffineSpaceOverField k n)
    (hZW : Z ≤ Closeds.closure ({y} : Set (AffineSpaceOverField k n))) :
    (@distanceTo (AffineSpaceOverField k n)
        (Hom.FiniteType.isNoetherian (affineSpaceOverFieldHom k n)) Z y : WithBot ℕ∞) =
      (((topologicalKrullDim
          (Closeds.closure ({y} : Set (AffineSpaceOverField k n)) :
            Set (AffineSpaceOverField k n))).unbotD 0 -
        (topologicalKrullDim (Z : Set (AffineSpaceOverField k n))).unbotD 0 : ℕ∞) :
          WithBot ℕ∞) := sorry

/-- If `dim (closure {y}) ≤ dim Z` but `closure {y}` is not contained in the
irreducible closed subset `Z` of affine space over a field, the distance is one. -/
theorem distanceToSubvariety_of_dim_le
    {k : Type u} [Field k] (n : ℕ) (Z : Closeds (AffineSpaceOverField k n))
    (hZ : IsIrreducible (Z : Set (AffineSpaceOverField k n))) (y : AffineSpaceOverField k n)
    (hdim : topologicalKrullDim
        (Closeds.closure ({y} : Set (AffineSpaceOverField k n)) :
          Set (AffineSpaceOverField k n)) ≤
      topologicalKrullDim (Z : Set (AffineSpaceOverField k n)))
    (hWZ : ¬Closeds.closure ({y} : Set (AffineSpaceOverField k n)) ≤ Z) :
    @distanceTo (AffineSpaceOverField k n)
      (Hom.FiniteType.isNoetherian (affineSpaceOverFieldHom k n)) Z y = 1 := sorry

/-- If `dim Z < dim (closure {y})` but the irreducible closed subset `Z` of affine
space over a field is not contained in `closure {y}`, the distance is
`dim (closure {y}) - dim Z + 1`. -/
theorem distanceToSubvariety_of_dim_gt
    {k : Type u} [Field k] (n : ℕ) (Z : Closeds (AffineSpaceOverField k n))
    (hZ : IsIrreducible (Z : Set (AffineSpaceOverField k n))) (y : AffineSpaceOverField k n)
    (hdim : topologicalKrullDim (Z : Set (AffineSpaceOverField k n)) <
      topologicalKrullDim
        (Closeds.closure ({y} : Set (AffineSpaceOverField k n)) :
          Set (AffineSpaceOverField k n)))
    (hZW : ¬Z ≤ Closeds.closure ({y} : Set (AffineSpaceOverField k n))) :
    (@distanceTo (AffineSpaceOverField k n)
        (Hom.FiniteType.isNoetherian (affineSpaceOverFieldHom k n)) Z y : WithBot ℕ∞) =
      (((topologicalKrullDim
          (Closeds.closure ({y} : Set (AffineSpaceOverField k n)) :
            Set (AffineSpaceOverField k n))).unbotD 0 -
        (topologicalKrullDim (Z : Set (AffineSpaceOverField k n))).unbotD 0 : ℕ∞) :
          WithBot ℕ∞) + 1 := sorry

/-- For a finite-type scheme over a field, the distance from `y` to a closed point
`z` is `dim (closure {y}) + t`, where `t` is the minimum length of a chain of
one-dimensional point closures connecting `z` to a closed point of `closure {y}`. -/
theorem distanceToClosedPoint_eq_add_minCurveChainLength
    {k : Type u} [Field k] (Y : SchemeOverField k) [Hom.FiniteType Y.hom]
    {y z : Y.left} (hz : IsClosed ({z} : Set Y.left)) (t : ℕ∞)
    (ht : t = sInf
      {d : ℕ∞ | ∃ C : Distance.Chain
          (⟨({z} : Set Y.left), hz⟩ : Closeds Y.left) y,
        d = C.length ∧ C.lower 0 = z ∧
          (∀ i, IsClosed ({C.lower i} : Set Y.left)) ∧
            ∀ i : Fin C.length,
              topologicalKrullDim (closure ({C.upper i.castSucc} : Set Y.left)) = 1}) :
    (@distanceTo Y.left (Hom.FiniteType.isNoetherian Y.hom)
        (⟨({z} : Set Y.left), hz⟩ : Closeds Y.left) y : WithBot ℕ∞) =
      topologicalKrullDim (closure ({y} : Set Y.left)) + (t : WithBot ℕ∞) := sorry

end AlgebraicGeometry.Scheme
