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
