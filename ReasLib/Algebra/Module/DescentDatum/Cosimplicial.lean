/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Amitsur.CosimplicialModule
public import ReasLib.Algebra.Module.DescentDatum

/-!
# Cosimplicial modules from module descent data

A module descent datum determines a module over the Amitsur cosimplicial ring.
Its degreewise modules are scalar extensions along the last vertex, and its
structure maps combine reindexing with the transition induced by descent.
-/

@[expose] public section

noncomputable section

open CategoryTheory ModuleCat Opposite
open scoped ChangeOfRings TensorProduct

universe u

namespace Module.DescentDatum

variable {R A N N' : Type u}
variable [CommRing R] [CommRing A] [Algebra R A]
variable [AddCommGroup N] [Module R N] [Module A N]
variable [IsScalarTower R A N] [SMulCommClass R A N]
variable [AddCommGroup N'] [Module R N'] [Module A N']
variable [IsScalarTower R A N'] [SMulCommClass R A N']

/-- The degree-`Δ` module obtained by extending `N` along the vertex `i`. -/
noncomputable def termAt (D : Module.DescentDatum R A N)
    (Δ : SimplexCategory) (i : Fin (Δ.len + 1)) :
    ModuleCat.{u} ((Algebra.Amitsur.cosimplicialCommRing R A).obj Δ) :=
  (ModuleCat.extendScalars (Algebra.Amitsur.vertex R A Δ i)).obj
    (ModuleCat.of A N)

/-- The generator map used to move scalar extension from vertex `i` to vertex `j`. -/
noncomputable def transitionGenerator (D : Module.DescentDatum R A N)
    (Δ : SimplexCategory) (i j : Fin (Δ.len + 1)) :
    ModuleCat.of A N ⟶
      (ModuleCat.restrictScalars (Algebra.Amitsur.vertex R A Δ i)).obj
        (termAt D Δ j) :=
  let q : A ⊗[R] N →ₗ[R]
      (ModuleCat.restrictScalars (algebraMap R A)).obj
        ((ModuleCat.restrictScalars (Algebra.Amitsur.vertex R A Δ j)).obj
          (termAt D Δ j)) :=
    TensorProduct.lift
      { toFun := fun a ↦
          { toFun := fun n ↦
              (ModuleCat.smul (termAt D Δ j) (Algebra.Amitsur.vertex R A Δ i a)).hom
                ((1 : (Algebra.Amitsur.cosimplicialCommRing R A).obj Δ) ⊗ₜ[A,
                  Algebra.Amitsur.vertex R A Δ j] n)
            map_add' := sorry
            map_smul' := sorry }
        map_add' := sorry
        map_smul' := sorry }
  ModuleCat.ofHom (X := ModuleCat.of A N)
    (Y := (ModuleCat.restrictScalars
      (Algebra.Amitsur.vertex R A Δ i)).obj (termAt D Δ j))
    { toFun := fun n ↦ q (D.equiv (n ⊗ₜ[R] (1 : A)))
      map_add' := sorry
      map_smul' := sorry }

/-- The inverse generator map used to move scalar extension from vertex `j` to vertex `i`. -/
noncomputable def transitionGeneratorInv (D : Module.DescentDatum R A N)
    (Δ : SimplexCategory) (i j : Fin (Δ.len + 1)) :
    ModuleCat.of A N ⟶
      (ModuleCat.restrictScalars (Algebra.Amitsur.vertex R A Δ j)).obj
        (termAt D Δ i) :=
  let q : N ⊗[R] A →ₗ[R]
      (ModuleCat.restrictScalars (algebraMap R A)).obj
        ((ModuleCat.restrictScalars (Algebra.Amitsur.vertex R A Δ i)).obj
          (termAt D Δ i)) :=
    TensorProduct.lift
      { toFun := fun n ↦
          { toFun := fun a ↦
              (ModuleCat.smul (termAt D Δ i) (Algebra.Amitsur.vertex R A Δ j a)).hom
                ((1 : (Algebra.Amitsur.cosimplicialCommRing R A).obj Δ) ⊗ₜ[A,
                  Algebra.Amitsur.vertex R A Δ i] n)
            map_add' := sorry
            map_smul' := sorry }
        map_add' := sorry
        map_smul' := sorry }
  ModuleCat.ofHom (X := ModuleCat.of A N)
    (Y := (ModuleCat.restrictScalars
      (Algebra.Amitsur.vertex R A Δ j)).obj (termAt D Δ i))
    { toFun := fun n ↦ q (D.equiv.symm ((1 : A) ⊗ₜ[R] n))
      map_add' := sorry
      map_smul' := sorry }

/-- Reindex the last-vertex module along a simplex morphism. -/
noncomputable def reindexLast (D : Module.DescentDatum R A N)
    {Δ Γ : SimplexCategory} (β : Δ ⟶ Γ) :
    termAt D Δ (Fin.last Δ.len) ⟶
      (ModuleCat.restrictScalars
        ((Algebra.Amitsur.cosimplicialCommRing R A).map β).hom).obj
          (termAt D Γ (β.toOrderHom (Fin.last Δ.len))) :=
  let target :=
    (ModuleCat.restrictScalars
      ((Algebra.Amitsur.cosimplicialCommRing R A).map β).hom).obj
        (termAt D Γ (β.toOrderHom (Fin.last Δ.len)))
  let generator : ModuleCat.of A N ⟶
      (ModuleCat.restrictScalars
        (Algebra.Amitsur.vertex R A Δ (Fin.last Δ.len))).obj target :=
    ModuleCat.ofHom (X := ModuleCat.of A N)
      (Y := (ModuleCat.restrictScalars
        (Algebra.Amitsur.vertex R A Δ (Fin.last Δ.len))).obj target)
      { toFun := fun n ↦
          (1 : (Algebra.Amitsur.cosimplicialCommRing R A).obj Γ) ⊗ₜ[A,
            Algebra.Amitsur.vertex R A Γ
              (β.toOrderHom (Fin.last Δ.len))] n
        map_add' := sorry
        map_smul' := sorry }
  ((ModuleCat.extendRestrictScalarsAdj
    (Algebra.Amitsur.vertex R A Δ (Fin.last Δ.len))).homEquiv _ _).symm generator

/-- The descent equivalence transported to one degree moves a vertex module to the last one. -/
noncomputable def transitionToLast (D : Module.DescentDatum R A N)
    (Γ : SimplexCategory) (i : Fin (Γ.len + 1)) :
    termAt D Γ i ≅ termAt D Γ (Fin.last Γ.len) where
  hom := ((ModuleCat.extendRestrictScalarsAdj
    (Algebra.Amitsur.vertex R A Γ i)).homEquiv _ _).symm
      (transitionGenerator D Γ i (Fin.last Γ.len))
  inv := ((ModuleCat.extendRestrictScalarsAdj
    (Algebra.Amitsur.vertex R A Γ (Fin.last Γ.len))).homEquiv _ _).symm
      (transitionGeneratorInv D Γ i (Fin.last Γ.len))
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- A simplex morphism acts by reindexing and then moving to the last vertex. -/
noncomputable def structureMap (D : Module.DescentDatum R A N)
    {Δ Γ : SimplexCategory} (β : Δ ⟶ Γ) :
    termAt D Δ (Fin.last Δ.len) ⟶
      (ModuleCat.restrictScalars
        ((Algebra.Amitsur.cosimplicialCommRing R A).map β).hom).obj
          (termAt D Γ (Fin.last Γ.len)) :=
  reindexLast D β ≫
    (ModuleCat.restrictScalars
      ((Algebra.Amitsur.cosimplicialCommRing R A).map β).hom).map
        (transitionToLast D Γ (β.toOrderHom (Fin.last Δ.len))).hom

/-- The module over the Amitsur cosimplicial ring determined by a descent datum. -/
noncomputable def cosimplicial (D : Module.DescentDatum R A N) :
    Algebra.Amitsur.CosimplicialModule R A where
  obj X := termAt D (unop (unop X)) (Fin.last (unop (unop X)).len)
  map f := structureMap D f.unop.unop
  map_id := sorry
  map_comp := sorry

/-- Evaluation of the associated cosimplicial module is the last-vertex term `N_{n,n}`. -/
theorem cosimplicial_obj (D : Module.DescentDatum R A N)
    (Δ : SimplexCategory) :
    Algebra.Amitsur.CosimplicialModule.eval R A (cosimplicial D) Δ =
      termAt D Δ (Fin.last Δ.len) := sorry

/-- The structure map is the descent transition after the canonical reindexing map. -/
theorem cosimplicial_map (D : Module.DescentDatum R A N)
    {Δ Γ : SimplexCategory} (β : Δ ⟶ Γ) :
    Algebra.Amitsur.CosimplicialModule.map R A (cosimplicial D) β =
      structureMap D β := sorry

namespace Hom

variable {D : Module.DescentDatum R A N} {D' : Module.DescentDatum R A N'}

/-- A morphism of descent data induces a morphism of the associated cosimplicial modules. -/
noncomputable def cosimplicial (f : Hom D D') :
    D.cosimplicial ⟶ D'.cosimplicial where
  app X := (ModuleCat.extendScalars
    (Algebra.Amitsur.vertex R A (unop (unop X))
      (Fin.last (unop (unop X)).len))).map (ModuleCat.ofHom f.hom)
  naturality := sorry

/-- The induced morphism is degreewise scalar extension of the underlying descent map. -/
theorem cosimplicial_app (f : Hom D D') (Δ : SimplexCategory) :
    Algebra.Amitsur.CosimplicialModule.app R A f.cosimplicial Δ =
      (ModuleCat.extendScalars
        (Algebra.Amitsur.vertex R A Δ (Fin.last Δ.len))).map
          (ModuleCat.ofHom f.hom) := sorry

/-- The identity descent morphism induces the identity cosimplicial-module morphism. -/
theorem cosimplicial_id (D : Module.DescentDatum R A N) :
    (Hom.id D).cosimplicial = 𝟙 D.cosimplicial := sorry

/-- The construction on descent morphisms preserves composition. -/
theorem cosimplicial_comp
    {N'' : Type u} [AddCommGroup N''] [Module R N''] [Module A N'']
    [IsScalarTower R A N''] [SMulCommClass R A N'']
    {D'' : Module.DescentDatum R A N''} (f : Hom D D') (g : Hom D' D'') :
    (Hom.comp f g).cosimplicial = f.cosimplicial ≫ g.cosimplicial := sorry

end Hom

end Module.DescentDatum
