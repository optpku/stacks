module

public import ReasLib.AlgebraicGeometry.CycleGroup.Reindex

open AlgebraicGeometry

universe u

/- The cycle-group reindexing homomorphism is provided by its reusable mathematical owner. -/
#check (AlgebraicGeometry.CycleGroup.reindex :
  ∀ {X : Scheme.{u}} (d : X → ℤ) {a b : ℤ}, a = b →
    AlgebraicGeometry.CycleGroup X d a →+ AlgebraicGeometry.CycleGroup X d b)

/- Reindexing along reflexivity is the identity homomorphism. -/
#check (AlgebraicGeometry.CycleGroup.reindex_refl :
  ∀ {X : Scheme.{u}} (d : X → ℤ) (a : ℤ),
    AlgebraicGeometry.CycleGroup.reindex d (rfl : a = a) =
      AddMonoidHom.id (AlgebraicGeometry.CycleGroup X d a))

/- Reindexing preserves the underlying algebraic cycle. -/
#check (AlgebraicGeometry.CycleGroup.toAlgebraicCycle_reindex :
  ∀ {X : Scheme.{u}} (d : X → ℤ) {a b : ℤ} (h : a = b)
      (alpha : AlgebraicGeometry.CycleGroup X d a),
    AlgebraicGeometry.CycleGroup.toAlgebraicCycle d b
        (AlgebraicGeometry.CycleGroup.reindex d h alpha) =
      AlgebraicGeometry.CycleGroup.toAlgebraicCycle d a alpha)
