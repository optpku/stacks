/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.DifferentialGraded.Algebra.Monoid.Equivalence
import Mathlib.Tactic.CrossRefAttribute

/-!
# Functoriality of differential graded algebra sheaves

Differential graded algebra sheaves are transported through their canonical presentation as monoid
objects in cochain complexes.  This makes `Functor.mapMon` and `Adjunction.mapMon` the reusable
owners; homogeneous multiplication and unit maps are not rebuilt for each geometric functor.
-/

@[expose] public section

open CategoryTheory
open scoped SheafOfModules.RingedSite.DifferentialGradedAlgebra

noncomputable section

universe uC vC wC uD vD wD

namespace SheafOfModules.RingedSite.DifferentialGradedAlgebra

section

variable {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
variable {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}
variable [JC.HasSheafCompose (forget₂ CommRingCat.{wC} RingCat.{wC})]
variable [JD.HasSheafCompose (forget₂ CommRingCat.{wD} RingCat.{wD})]
variable [HasWeakSheafify JC AddCommGrpCat.{wC}]
variable [JC.WEqualsLocallyBijective AddCommGrpCat.{wC}]
variable [HasWeakSheafify JD AddCommGrpCat.{wD}]
variable [JD.WEqualsLocallyBijective AddCommGrpCat.{wD}]
variable [UnivLE.{max uC vC, wC}] [UnivLE.{max uD vD, wD}]
variable {OC : Sheaf JC CommRingCat.{wC}}
variable {OD : Sheaf JD CommRingCat.{wD}}

section Map

variable (F : CochainComplex (moduleCategory (J := JC) (𝒪 := OC)) ℤ ⥤
  CochainComplex (moduleCategory (J := JD) (𝒪 := OD)) ℤ)
variable [F.LaxMonoidal]

/-- A lax monoidal functor on cochain complexes transports differential graded algebra sheaves by
the canonical monoid-object presentation. -/
@[stacks 0FRE "lax monoidal transport of differential graded algebras"]
noncomputable def map : DGA(OC) ⥤ DGA(OD) :=
  toMonFunctor (𝒪 := OC) ⋙ F.mapMon ⋙ ofMonFunctor (𝒪 := OD)

/-- A morphism out of a transported differential graded algebra, expressed as the corresponding
morphism from the transported monoid object.  The comparison is the inverse of the canonical
monoid-side counit, so no choice of multiplication or unit data is involved. -/
noncomputable def mapHomToMon {A : DGA(OC)} {B : DGA(OD)}
    (φ : (map F).obj A ⟶ B) :
    F.mapMon.obj A.toMon ⟶ B.toMon :=
  (toMonCounitIso (F.mapMon.obj A.toMon)).inv ≫ toMonFunctor.map φ

/-- The underlying cochain map of `mapHomToMon F φ` is the underlying map of `φ`. -/
@[simp]
theorem mapHomToMon_hom {A : DGA(OC)} {B : DGA(OD)}
    (φ : (map F).obj A ⟶ B) :
    (mapHomToMon F φ).hom = φ.hom := sorry

/-- The underlying cochain complex of a transported differential graded algebra is the image of
its original underlying cochain complex. -/
@[simp]
theorem map_obj_toComplex (A : DGA(OC)) :
    ((map F).obj A).toComplex = F.obj A.toComplex := sorry

/-- Transport of a differential graded algebra morphism uses the image of its underlying cochain
map. -/
@[simp]
theorem map_map_hom {A B : DGA(OC)} (f : A ⟶ B) :
    ((map F).map f).hom = F.map f.hom := sorry

end Map

section Adjunction

variable (F : CochainComplex (moduleCategory (J := JC) (𝒪 := OC)) ℤ ⥤
  CochainComplex (moduleCategory (J := JD) (𝒪 := OD)) ℤ)

variable {F}
variable (G : CochainComplex (moduleCategory (J := JD) (𝒪 := OD)) ℤ ⥤
  CochainComplex (moduleCategory (J := JC) (𝒪 := OC)) ℤ)
variable [F.Monoidal] [G.LaxMonoidal]

/-- A monoidal adjunction on cochain complexes lifts canonically to differential graded algebra
sheaves. -/
@[stacks 0FRE "differential graded algebra adjunction"]
noncomputable def mapAdjunction (adj : F ⊣ G) [adj.IsMonoidal] :
    map (C := C) (D := D) (JC := JC) (JD := JD) (OC := OC) (OD := OD) F ⊣
      map (C := D) (D := C) (JC := JD) (JD := JC) (OC := OD) (OD := OC) G :=
  ((toMonEquivalence (𝒪 := OC)).toAdjunction.comp adj.mapMon).comp
    (toMonEquivalence (𝒪 := OD)).symm.toAdjunction

/-- The Hom equivalence induced by the lifted adjunction on differential graded algebra sheaves. -/
@[stacks 0FRE "differential graded algebra Hom equivalence"]
noncomputable def mapHomEquiv (adj : F ⊣ G) [adj.IsMonoidal]
    (A : DGA(OC)) (B : DGA(OD)) :
    ((map (C := C) (D := D) (JC := JC) (JD := JD)
      (OC := OC) (OD := OD) F).obj A ⟶ B) ≃
      (A ⟶ (map (C := D) (D := C) (JC := JD) (JD := JC)
        (OC := OD) (OD := OC) G).obj B) :=
  (mapAdjunction (C := C) (D := D) (JC := JC) (JD := JD)
    (OC := OC) (OD := OD) G adj).homEquiv A B

end Adjunction

end

end SheafOfModules.RingedSite.DifferentialGradedAlgebra

end
