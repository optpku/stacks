module

public import ReasLib.AlgebraicGeometry.Scheme.OverField.Multicross

@[expose] public section

universe u

namespace AlgebraicGeometry.SchemeOverField

#check (isMulticrossPoint :
  ∀ {k : Type u} [Field k] [IsAlgClosed k] (X : SchemeOverField k) (x : X.left)
    (n : ℕ), Prop)
#check (isMulticrossPoint_iff :
  ∀ {k : Type u} [Field k] [IsAlgClosed k] (X : SchemeOverField k) (x : X.left) (n : ℕ),
    isMulticrossPoint X x n ↔
      x ∈ closedPoints X.left ∧ 2 ≤ n ∧
        Nonempty
          (AdicCompletion (IsLocalRing.maximalIdeal (stalkRing X x)) (stalkRing X x) ≃ₐ[k]
            Multicross.ring k n))
#check (isMulticrossSingularity :
  ∀ {k : Type u} [Field k] [IsAlgClosed k] (X : SchemeOverField k) (x : X.left), Prop)
#check (isMulticrossSingularity_iff :
  ∀ {k : Type u} [Field k] [IsAlgClosed k] (X : SchemeOverField k) (x : X.left),
    isMulticrossSingularity X x ↔
      x ∈ closedPoints X.left ∧
        ∃ n : ℕ, 2 ≤ n ∧
          Nonempty
            (AdicCompletion (IsLocalRing.maximalIdeal (stalkRing X x)) (stalkRing X x) ≃ₐ[k]
              Multicross.ring k n))
#check (isMulticrossPoint.isMulticrossSingularity :
  ∀ {k : Type u} [Field k] [IsAlgClosed k] {X : SchemeOverField k} {x : X.left} {n : ℕ},
    isMulticrossPoint X x n → isMulticrossSingularity X x)

end AlgebraicGeometry.SchemeOverField
