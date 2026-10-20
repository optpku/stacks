module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.AffineLineQuotient.Presentation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FunctorOfPoints
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.QuasiCompact
public import ReasLib.AlgebraicGeometry.Scheme.PreRelation.QuotientSheaf

/-!
# The algebraic space 𝔸¹_k / ℤ

The quotient of the affine line by integer translation has a Type-`u` functor of
points and a canonical étale atlas from the affine line, making it quasi-compact.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits
open AlgebraicGeometry.Scheme

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.AffineLineQuotient

/-- The atlas `U ⟶ U / ℤ` is the canonical projection to the quotient sheaf. -/
def atlas (k : Type u) [Field k] [CharZero k] :
    yoneda.obj (cover k) ⟶ (preRelation k).smallEtaleQuotientSheaf.obj :=
  (preRelation k).smallEtaleQuotientSheafMk

/-- The atlas is the quotient projection of the translation pre-relation followed by
sheafification. -/
theorem atlas_eq (k : Type u) [Field k] [CharZero k] :
    atlas k = (preRelation k).smallEtaleQuotientSheafMk := by
  rfl

/-- The étale quotient sheaf `U / ℤ` satisfies fppf descent. -/
theorem functorOfPoints_isSheaf (k : Type u) [Field k] [CharZero k] :
    Presheaf.IsSheaf (Scheme.fppfTopology.over (base k)) (preRelation k).smallEtaleQuotientSheaf.obj := sorry

/-- The diagonal of `U / ℤ` is representable by schemes (Spaces, Theorem 02WW): over a test
pair that lifts to `(a, b) : T ⟶ U ×_S U`, the represented fibre product is `T ×_{U ×_S U} R`;
in general it is obtained from these by étale descent. -/
theorem functorOfPoints_representableDiagonal (k : Type u) [Field k] [CharZero k] :
    yoneda.relativelyRepresentable (Limits.diag (preRelation k).smallEtaleQuotientSheaf.obj) := sorry

/-- The atlas `U ⟶ U / ℤ` is representable and étale. Its represented pullbacks are those
induced by the represented diagonal (`Functor.relativelyRepresentable.of_diag`). -/
theorem atlas_etale (k : Type u) [Field k] [CharZero k] :
    (MorphismProperty.over (@Etale)).presheaf (atlas k) :=
  ⟨Functor.relativelyRepresentable.of_diag (functorOfPoints_representableDiagonal k) (atlas k),
    sorry⟩

/-- The atlas `U ⟶ U / ℤ` is étale-locally surjective. -/
theorem atlas_locallySurjective (k : Type u) [Field k] [CharZero k] :
    Presheaf.IsLocallySurjective (Scheme.etaleTopology.over (base k)) (atlas k) := sorry

/-- The algebraic space `U / ℤ` over `Spec k`, presented by the translation equivalence
relation on the affine line, with the affine line as its atlas. -/
def space (k : Type u) [Field k] [CharZero k] : AlgebraicSpace (base k) :=
  ofFunctor (preRelation k).smallEtaleQuotientSheaf.obj (functorOfPoints_isSheaf k)
    (functorOfPoints_representableDiagonal k)
    ⟨cover k, atlas k, atlas_etale k, atlas_locallySurjective k⟩

/-- The functor of points of `space k` is the étale sheafification of the objectwise quotient of
`T`-points of `U` by integer translation. -/
theorem space_functorOfPoints (k : Type u) [Field k] [CharZero k] :
    (space k).functorOfPoints = (preRelation k).smallEtaleQuotientSheaf.obj := by
  rfl

/-- The quotient of the affine line over a characteristic-zero field by integer
translation is a quasi-compact algebraic space. -/
instance instIsQuasiCompact (k : Type u) [Field k] [CharZero k] :
    IsQuasiCompact (space k) where
  exists_compact_etaleCover :=
    ⟨cover k, atlas k, atlas_etale k, atlas_locallySurjective k, inferInstance⟩

end AlgebraicGeometry.AlgebraicSpace.AffineLineQuotient
