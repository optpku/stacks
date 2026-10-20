module

public import ReasLib.Algebra.Homology.CochainComplex.KFlat
public import ReasLib.Algebra.Homology.CochainComplex.KFlat.Relative.Isomorphism
public import ReasLib.Algebra.Homology.HomologicalComplex.KFlat.Isomorphism

/-!
# Isomorphism transport for K-flat complexes

The K-flat predicate is owned by `HomologicalComplex.KFlat`; this leaf specializes its standard
isomorphism transport API to cochain complexes.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u v

namespace CochainComplex

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [MonoidalCategory C] [MonoidalPreadditive C]

namespace IsKFlat

/-- K-flatness transports from the source to the target of an isomorphism of cochain complexes. -/
theorem of_iso {K L : CochainComplex C ℤ} (hK : K.IsKFlat) (e : K ≅ L) :
    L.IsKFlat := sorry

/-- Isomorphic cochain complexes are simultaneously K-flat for the ambient monoidal tensor
product. -/
theorem iff_of_iso {K L : CochainComplex C ℤ} (e : K ≅ L) :
    K.IsKFlat ↔ L.IsKFlat := sorry

end IsKFlat

end CochainComplex
