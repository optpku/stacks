/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

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

/-- The algebraic space `U / ℤ` over `Spec k`, presented by the translation equivalence
relation on the affine line. -/
def space (k : Type u) [Field k] [CharZero k] : AlgebraicSpace (base k) where
  functorOfPoints := (preRelation k).smallEtaleQuotientSheaf.obj
  isSheaf := sorry
  representableDiagonal := sorry
  atlas := ⟨cover k, (preRelation k).smallEtaleQuotientSheafMk, sorry, sorry⟩

/-- The functor of points of `space k` is the étale sheafification of the objectwise quotient of
`T`-points of `U` by integer translation. -/
theorem space_functorOfPoints (k : Type u) [Field k] [CharZero k] :
    (space k).functorOfPoints = (preRelation k).smallEtaleQuotientSheaf.obj := by
  rfl

/-- The atlas `U ⟶ U / ℤ` is the canonical projection to the quotient sheaf. -/
def atlas (k : Type u) [Field k] [CharZero k] :
    yoneda.obj (cover k) ⟶ (space k).functorOfPoints :=
  (preRelation k).smallEtaleQuotientSheafMk

/-- The atlas is the quotient projection of the translation pre-relation followed by
sheafification. -/
theorem atlas_eq (k : Type u) [Field k] [CharZero k] :
    atlas k = (preRelation k).smallEtaleQuotientSheafMk := by
  rfl

/-- The atlas `U ⟶ U / ℤ` is representable and étale. -/
theorem atlas_etale (k : Type u) [Field k] [CharZero k] :
    (MorphismProperty.over (@Etale)).presheaf (atlas k) := sorry

/-- The atlas `U ⟶ U / ℤ` is étale-locally surjective. -/
theorem atlas_locallySurjective (k : Type u) [Field k] [CharZero k] :
    Presheaf.IsLocallySurjective (Scheme.etaleTopology.over (base k)) (atlas k) := sorry

/-- The quotient of the affine line over a characteristic-zero field by integer
translation is a quasi-compact algebraic space. -/
instance instIsQuasiCompact (k : Type u) [Field k] [CharZero k] :
    IsQuasiCompact (space k) where
  exists_compact_etaleCover :=
    ⟨cover k, atlas k, atlas_etale k, atlas_locallySurjective k, inferInstance⟩

end AlgebraicGeometry.AlgebraicSpace.AffineLineQuotient
