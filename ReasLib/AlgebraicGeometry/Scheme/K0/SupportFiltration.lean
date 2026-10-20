/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.K0
public import ReasLib.AlgebraicGeometry.Scheme.Module.FilteredK0
public import ReasLib.CategoryTheory.Abelian.GrothendieckGroup
public import ReasLib.CategoryTheory.Abelian.GrothendieckGroup.Property

@[expose] public section

open CategoryTheory
open scoped BigOperators DirectSum TensorProduct Topology

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.K0'

variable {S X : Scheme.{u}} (f : X ⟶ S) [UniversallyCatenary S]
  [LocallyOfFiniteType f] (δ : S → ℤ) [IsDimensionFunction δ]

/-- Short-exact relations in `Coh≤k(X)` vanish in coherent `K₀'(X)`. -/
theorem fromUpper_relations (k : ℤ) :
    AbelianK0.relations
        (RingedSpace.CohLE X.toRingedSpace (f.relativeDimensionFunction δ) k) ≤
      (FreeAbelianGroup.lift fun
          F : RingedSpace.CohLE X.toRingedSpace (f.relativeDimensionFunction δ) k ↦
        ObjectProperty.GrothendieckGroup.of
          (SheafOfModules.isCoherent X.toRingedSpace.ringCatSheaf) F.obj).ker :=
  sorry

/-- The canonical map `K₀(Coh≤k(X)) → K₀'(X)` sending a bounded-support coherent sheaf to
its class in coherent `K₀`. -/
noncomputable def fromUpper (k : ℤ) :
    AbelianK0 (RingedSpace.CohLE X.toRingedSpace (f.relativeDimensionFunction δ) k) →+
      @K0' X (LocallyOfFiniteType.isLocallyNoetherian f) :=
  AbelianK0.lift
    (fun F ↦
      ObjectProperty.GrothendieckGroup.of
        (SheafOfModules.isCoherent X.toRingedSpace.ringCatSheaf) F.obj)
    (fromUpper_relations f δ k)

/-- `fromUpper` sends an object of `Coh≤k(X)` to the coherent Grothendieck class of its
underlying sheaf. -/
theorem fromUpper_of (k : ℤ)
    (F : RingedSpace.CohLE X.toRingedSpace (f.relativeDimensionFunction δ) k) :
    fromUpper f δ k (AbelianK0.of F) =
      ObjectProperty.GrothendieckGroup.of
        (SheafOfModules.isCoherent X.toRingedSpace.ringCatSheaf) F.obj :=
  sorry

/-- The filtration by dimension of supports: `F_k K₀'(X)` is the image of
`K₀(Coh≤k(X)) → K₀'(X)`. -/
noncomputable def supportFiltration (k : ℤ) :
    AddSubgroup (@K0' X (LocallyOfFiniteType.isLocallyNoetherian f)) :=
  (fromUpper f δ k).range

/-- Membership in `F_k K₀'(X)` is being the image of a class from `K₀(Coh≤k(X))`. -/
theorem mem_supportFiltration (k : ℤ)
    (x : @K0' X (LocallyOfFiniteType.isLocallyNoetherian f)) :
    x ∈ supportFiltration f δ k ↔ ∃ y, fromUpper f δ k y = x :=
  sorry

/-- The support filtration is increasing in the dimension bound. -/
theorem supportFiltration_mono {k l : ℤ} (h : k ≤ l) :
    supportFiltration f δ k ≤ supportFiltration f δ l :=
  sorry

/-- The associated graded piece `gr_k K₀'(X) = F_k K₀'(X) / F_{k-1} K₀'(X)`. -/
abbrev Graded (k : ℤ) : Type (u + 1) :=
  supportFiltration f δ k ⧸
    AddSubgroup.comap (supportFiltration f δ k).subtype (supportFiltration f δ (k - 1))

/-- `Graded` is the quotient of `F_k` by the inverse image of `F_{k-1}`. -/
theorem Graded_def (k : ℤ) :
    Graded f δ k =
      (supportFiltration f δ k ⧸
        AddSubgroup.comap (supportFiltration f δ k).subtype
          (supportFiltration f δ (k - 1))) :=
  sorry

/-- The class of an element of `F_k K₀'(X)` in the associated graded piece. -/
noncomputable def Graded.mk (k : ℤ) (x : supportFiltration f δ k) :
    Graded f δ k :=
  QuotientAddGroup.mk' _ x

/-- `Graded.mk` is the canonical quotient class. -/
theorem Graded.mk_def (k : ℤ) (x : supportFiltration f δ k) :
    Graded.mk f δ k x = QuotientAddGroup.mk' _ x :=
  sorry

end AlgebraicGeometry.Scheme.K0'

