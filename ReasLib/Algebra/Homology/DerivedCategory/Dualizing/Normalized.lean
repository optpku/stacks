/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import ReasLib.Algebra.Homology.DerivedCategory.Dualizing
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleEmbedding

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace CategoryTheory.DerivedCategory

variable {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
variable [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))]

/-- A normalized dualizing complex is dualizing and has residue-field derived internal Hom
isomorphic to the residue field concentrated in degree zero. -/
structure IsNormalizedDualizingComplex
    (K : DerivedCategory (ModuleCat.{u} A))
    (H : MonoidalClosed (DerivedCategory (ModuleCat.{u} A))) : Prop where
  /-- The underlying complex is dualizing. -/
  isDualizingComplex : K.IsDualizingComplex H
  /-- The derived internal Hom from the residue field recovers the residue field in degree zero. -/
  residueFieldRHom :
    Nonempty
      (((MonoidalClosed.ihomOf H
        (ModuleCat.single0 (ModuleCat.of A (IsLocalRing.ResidueField A)))).obj K) ≅
          ModuleCat.single0 (ModuleCat.of A (IsLocalRing.ResidueField A)))

namespace IsNormalizedDualizingComplex

/-- Construct a normalized dualizing complex from duality and residue-field normalization. -/
def of
    {K : DerivedCategory (ModuleCat.{u} A)}
    {H : MonoidalClosed (DerivedCategory (ModuleCat.{u} A))}
    (hdualizing : K.IsDualizingComplex H)
    (hnormalized :
      Nonempty
        (((MonoidalClosed.ihomOf H
          (ModuleCat.single0 (ModuleCat.of A (IsLocalRing.ResidueField A)))).obj K) ≅
            ModuleCat.single0 (ModuleCat.of A (IsLocalRing.ResidueField A)))) :
    K.IsNormalizedDualizingComplex H := sorry

end IsNormalizedDualizingComplex

/-- A normalized dualizing complex for the canonical module `RHom` presentation.  The selected
closed presentation remains available through `C.comparison.closed`; the normalization datum here
is anchored to the canonical `RHom` object, so it cannot be changed by transporting a closed
structure along an unrelated equivalence. -/
structure IsCanonicalNormalizedDualizingComplex
    (K : DerivedCategory (ModuleCat.{u} A))
    (C : CanonicalClosedPresentation (A := A)) : Prop where
  /-- The underlying complex is dualizing for the canonical `RHom` presentation. -/
  isCanonicalDualizingComplex : K.IsCanonicalDualizingComplex C
  /-- Canonical derived `RHom` from the residue field is concentrated in degree zero. -/
  residueFieldRHom :
    Nonempty
      ((InternalHom.RHom.obj (A := A)
        (ModuleCat.single0 (ModuleCat.of A (IsLocalRing.ResidueField A))) K) ≅
          ModuleCat.single0 (ModuleCat.of A (IsLocalRing.ResidueField A)))

namespace IsCanonicalNormalizedDualizingComplex

/-- Construct the canonical normalized dualizing-complex property from its two defining data. -/
def of
    {K : DerivedCategory (ModuleCat.{u} A)}
    {C : CanonicalClosedPresentation (A := A)}
    (hdualizing : K.IsCanonicalDualizingComplex C)
    (hnormalized :
      Nonempty
        ((InternalHom.RHom.obj (A := A)
          (ModuleCat.single0 (ModuleCat.of A (IsLocalRing.ResidueField A))) K) ≅
            ModuleCat.single0 (ModuleCat.of A (IsLocalRing.ResidueField A)))) :
    K.IsCanonicalNormalizedDualizingComplex C :=
  ⟨hdualizing, hnormalized⟩

/-- Canonical normalization implies normalization for the selected closed presentation carried by
the canonical comparison.  The comparison and the regular-unit isomorphism are the only bridge;
the selected predicate itself is retained for APIs that intentionally work with a chosen
presentation. -/
theorem toSelected
    {K : DerivedCategory (ModuleCat.{u} A)}
    {C : CanonicalClosedPresentation (A := A)}
    (hK : K.IsCanonicalNormalizedDualizingComplex C) :
    K.IsNormalizedDualizingComplex C.comparison.closed := sorry

end IsCanonicalNormalizedDualizingComplex

/-- The canonical normalized property is equivalent to canonical duality together with canonical
residue-field normalization. -/
theorem isCanonicalNormalizedDualizingComplex_iff
    (K : DerivedCategory (ModuleCat.{u} A))
    (C : CanonicalClosedPresentation (A := A)) :
    K.IsCanonicalNormalizedDualizingComplex C ↔
      K.IsCanonicalDualizingComplex C ∧
        Nonempty
          ((InternalHom.RHom.obj (A := A)
            (ModuleCat.single0 (ModuleCat.of A (IsLocalRing.ResidueField A))) K) ≅
              ModuleCat.single0 (ModuleCat.of A (IsLocalRing.ResidueField A))) := by
  constructor
  · intro h
    exact ⟨h.isCanonicalDualizingComplex, h.residueFieldRHom⟩
  · rintro ⟨hdualizing, hnormalized⟩
    exact ⟨hdualizing, hnormalized⟩

/-- A complex is normalized dualizing exactly when it is dualizing and its derived internal Hom
from the residue field is the residue field concentrated in degree zero. -/
theorem isNormalizedDualizingComplex_iff
    (K : DerivedCategory (ModuleCat.{u} A))
    (H : MonoidalClosed (DerivedCategory (ModuleCat.{u} A))) :
    K.IsNormalizedDualizingComplex H ↔
      K.IsDualizingComplex H ∧
        Nonempty
          (((MonoidalClosed.ihomOf H
            (ModuleCat.single0 (ModuleCat.of A (IsLocalRing.ResidueField A)))).obj K) ≅
              ModuleCat.single0 (ModuleCat.of A (IsLocalRing.ResidueField A))) := sorry

end CategoryTheory.DerivedCategory
