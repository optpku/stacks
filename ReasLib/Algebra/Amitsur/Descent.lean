/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Amitsur.CosimplicialModule
public import ReasLib.Algebra.Category.ModuleCat.Descent.BaseExtension
public import ReasLib.Algebra.Category.ModuleCat.Presheaf.Cosimplicial

/-!
# Cartesian Amitsur modules from descent data

This file constructs the functor from module descent data to cartesian modules over the
Amitsur cosimplicial algebra and packages it as an equivalence of categories.
-/

@[expose] public section

noncomputable section

open CategoryTheory Opposite
open scoped ChangeOfRings TensorProduct

universe u

namespace Algebra.Amitsur.Descent

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]

/-- The unique module component of canonical descent data along `R → A`. -/
abbrev component (D : ModuleCat.DescentData (Algebra.ofId R A).toRingHom) :
    ModuleCat.{u} A :=
  D.obj PUnit.unit

/-- The component abbreviation recovers the unique object of the singleton descent family. -/
theorem component_def (D : ModuleCat.DescentData (Algebra.ofId R A).toRingHom) :
    component D = D.obj PUnit.unit := sorry

/-- The degree-`Δ` scalar extension of the unique module component of canonical descent data
along the vertex `i`. -/
noncomputable abbrev termAt
    (D : ModuleCat.DescentData (Algebra.ofId R A).toRingHom)
    (Δ : SimplexCategory) (i : Fin (Δ.len + 1)) :
    ModuleCat.{u} ((Algebra.Amitsur.cosimplicialCommRing R A).obj Δ) :=
  (ModuleCat.extendScalars (Algebra.Amitsur.vertex R A Δ i)).obj (component D)

/-- `termAt` is the scalar extension of the unique component of the descent datum. -/
theorem termAt_def (D : ModuleCat.DescentData (Algebra.ofId R A).toRingHom)
    (Δ : SimplexCategory) (i : Fin (Δ.len + 1)) :
    termAt D Δ i =
      (ModuleCat.extendScalars (Algebra.Amitsur.vertex R A Δ i)).obj
        (component D) := sorry

/-- Canonical descent data identify the scalar extensions along any two vertices of one
Amitsur degree. -/
noncomputable def transitionToLast
    (D : ModuleCat.DescentData (Algebra.ofId R A).toRingHom)
    (Γ : SimplexCategory) (i : Fin (Γ.len + 1)) :
    termAt D Γ i ≅ termAt D Γ (Fin.last Γ.len) :=
  D.iso
    ((CommRingCat.ofHom
      (algebraMap R ((Algebra.Amitsur.cosimplicialAlgebra R A).obj Γ))).op)
    ((CommRingCat.ofHom (Algebra.Amitsur.vertex R A Γ i)).op)
    ((CommRingCat.ofHom
      (Algebra.Amitsur.vertex R A Γ (Fin.last Γ.len))).op)
    (Algebra.Amitsur.vertex_overBase Γ i)
    (Algebra.Amitsur.vertex_overBase Γ (Fin.last Γ.len))

/-- The forward map of `transitionToLast` is the transition supplied by the descent datum. -/
theorem transitionToLast_hom
    (D : ModuleCat.DescentData (Algebra.ofId R A).toRingHom)
    (Γ : SimplexCategory) (i : Fin (Γ.len + 1)) :
    (transitionToLast D Γ i).hom =
      D.hom
        ((CommRingCat.ofHom
          (algebraMap R ((Algebra.Amitsur.cosimplicialAlgebra R A).obj Γ))).op)
        ((CommRingCat.ofHom (Algebra.Amitsur.vertex R A Γ i)).op)
        ((CommRingCat.ofHom
          (Algebra.Amitsur.vertex R A Γ (Fin.last Γ.len))).op)
        (Algebra.Amitsur.vertex_overBase Γ i)
        (Algebra.Amitsur.vertex_overBase Γ (Fin.last Γ.len)) := sorry

/-- Reindex the last-vertex module along a simplex morphism. -/
noncomputable def reindexLast
    (D : ModuleCat.DescentData (Algebra.ofId R A).toRingHom)
    {Δ Γ : SimplexCategory} (β : Δ ⟶ Γ) :
    termAt D Δ (Fin.last Δ.len) ⟶
      (ModuleCat.restrictScalars
        ((Algebra.Amitsur.cosimplicialCommRing R A).map β).hom).obj
          (termAt D Γ (β.toOrderHom (Fin.last Δ.len))) :=
  let target :=
    (ModuleCat.restrictScalars
      ((Algebra.Amitsur.cosimplicialCommRing R A).map β).hom).obj
        (termAt D Γ (β.toOrderHom (Fin.last Δ.len)))
  let generator : component D ⟶
      (ModuleCat.restrictScalars
        (Algebra.Amitsur.vertex R A Δ (Fin.last Δ.len))).obj target :=
    (ModuleCat.extendRestrictScalarsAdj
      (Algebra.Amitsur.vertex R A Γ
        (β.toOrderHom (Fin.last Δ.len)))).unit.app (component D) ≫
      (ModuleCat.restrictScalarsComp'App
        (Algebra.Amitsur.vertex R A Δ (Fin.last Δ.len))
        ((Algebra.Amitsur.cosimplicialCommRing R A).map β).hom
        (Algebra.Amitsur.vertex R A Γ
          (β.toOrderHom (Fin.last Δ.len)))
        (Algebra.Amitsur.vertex_map β (Fin.last Δ.len))
        (termAt D Γ (β.toOrderHom (Fin.last Δ.len)))).hom
  ((ModuleCat.extendRestrictScalarsAdj
    (Algebra.Amitsur.vertex R A Δ (Fin.last Δ.len))).homEquiv _ _).symm generator

/-- The Amitsur structure map first reindexes and then applies the descent transition. -/
noncomputable def structureMap
    (D : ModuleCat.DescentData (Algebra.ofId R A).toRingHom)
    {Δ Γ : SimplexCategory} (β : Δ ⟶ Γ) :
    termAt D Δ (Fin.last Δ.len) ⟶
      (ModuleCat.restrictScalars
        ((Algebra.Amitsur.cosimplicialCommRing R A).map β).hom).obj
          (termAt D Γ (Fin.last Γ.len)) :=
  reindexLast D β ≫
    (ModuleCat.restrictScalars
      ((Algebra.Amitsur.cosimplicialCommRing R A).map β).hom).map
        (transitionToLast D Γ (β.toOrderHom (Fin.last Δ.len))).hom

/-- Canonical module descent data determine a module over the Amitsur cosimplicial algebra. -/
noncomputable def cosimplicial
    (D : ModuleCat.DescentData (Algebra.ofId R A).toRingHom) :
    CosimplicialAlgebra.Module (Algebra.Amitsur.cosimplicialAlgebra R A) where
  obj X := termAt D (unop (unop X)) (Fin.last (unop (unop X)).len)
  map f := structureMap D f.unop.unop
  map_id := sorry
  map_comp := sorry

/-- Evaluation of the associated cosimplicial module is its last-vertex scalar extension. -/
theorem cosimplicial_obj
    (D : ModuleCat.DescentData (Algebra.ofId R A).toRingHom)
    (Δ : SimplexCategory) :
    CosimplicialAlgebra.Module.eval (cosimplicial D) Δ =
      termAt D Δ (Fin.last Δ.len) := sorry

/-- A morphism of canonical descent data induces a morphism of Amitsur cosimplicial modules. -/
noncomputable def cosimplicialMap
    {D E : ModuleCat.DescentData (Algebra.ofId R A).toRingHom} (f : D ⟶ E) :
    cosimplicial D ⟶ cosimplicial E where
  app X := (ModuleCat.extendScalars
    (Algebra.Amitsur.vertex R A (unop (unop X))
      (Fin.last (unop (unop X)).len))).map (f.hom PUnit.unit)
  naturality := sorry

/-- The component of `cosimplicialMap` is scalar extension of the unique descent-data
component. -/
theorem cosimplicialMap_app
    {D E : ModuleCat.DescentData (Algebra.ofId R A).toRingHom} (f : D ⟶ E)
    (Δ : SimplexCategory) :
    PresheafOfModules.Hom.app (cosimplicialMap f) (op (op Δ)) =
      (ModuleCat.extendScalars
        (Algebra.Amitsur.vertex R A Δ (Fin.last Δ.len))).map
          (f.hom PUnit.unit) := sorry

/-- The functor from canonical module descent data to modules over the Amitsur cosimplicial
algebra. -/
noncomputable def toModule : ModuleCat.DescentData (Algebra.ofId R A).toRingHom ⥤
    CosimplicialAlgebra.Module (Algebra.Amitsur.cosimplicialAlgebra R A) where
  obj := cosimplicial
  map := cosimplicialMap
  map_id := sorry
  map_comp := sorry

/-- Every Amitsur cosimplicial module obtained from canonical descent data is cartesian. -/
theorem toModule_isCartesian
    (D : ModuleCat.DescentData (Algebra.ofId R A).toRingHom) :
    CosimplicialAlgebra.Module.IsCartesian ((toModule).obj D) := sorry

/-- The functor from canonical module descent data to cartesian modules over the Amitsur
cosimplicial algebra. -/
noncomputable def toCartesian : ModuleCat.DescentData (Algebra.ofId R A).toRingHom ⥤
    CosimplicialAlgebra.CartesianModule (Algebra.Amitsur.cosimplicialAlgebra R A) :=
  ObjectProperty.lift
    (fun M : CosimplicialAlgebra.Module (Algebra.Amitsur.cosimplicialAlgebra R A) ↦
      CosimplicialAlgebra.Module.IsCartesian M) toModule toModule_isCartesian

/-- The canonical functor from module descent data to cartesian Amitsur modules is an
equivalence. -/
instance toCartesian_isEquivalence :
    (toCartesian : ModuleCat.DescentData (Algebra.ofId R A).toRingHom ⥤
      CosimplicialAlgebra.CartesianModule
        (Algebra.Amitsur.cosimplicialAlgebra R A)).IsEquivalence := sorry

/-- The inverse functor recovering canonical module descent data from a cartesian Amitsur
module. -/
noncomputable def ofCartesian :
    CosimplicialAlgebra.CartesianModule (Algebra.Amitsur.cosimplicialAlgebra R A) ⥤
      ModuleCat.DescentData (Algebra.ofId R A).toRingHom :=
  (toCartesian (R := R) (A := A)).inv

/-- Canonical module descent data are equivalent to cartesian modules over the Amitsur
cosimplicial algebra. -/
noncomputable def equivalence :
    ModuleCat.DescentData (Algebra.ofId R A).toRingHom ≌
      CosimplicialAlgebra.CartesianModule (Algebra.Amitsur.cosimplicialAlgebra R A) :=
  (toCartesian (R := R) (A := A)).asEquivalence

/-- The forward functor of `equivalence` is `toCartesian`. -/
theorem equivalence_functor :
    (equivalence (R := R) (A := A)).functor = toCartesian := sorry

/-- The inverse functor of `equivalence` is `ofCartesian`. -/
theorem equivalence_inverse :
    (equivalence (R := R) (A := A)).inverse = ofCartesian := sorry

end Algebra.Amitsur.Descent
