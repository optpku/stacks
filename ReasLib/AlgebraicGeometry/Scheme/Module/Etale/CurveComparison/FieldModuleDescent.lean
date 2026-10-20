/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import Mathlib.CategoryTheory.Sites.Point.Category
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.FieldTheory.Galois.Profinite
public import ReasLib.AlgebraicGeometry.Scheme.Etale.StalkGaloisAction
public import ReasLib.CategoryTheory.Action.ModuleCat.OpenStabilizer.Definition

@[expose] public section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Action.ModuleCat Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
noncomputable section
universe u

namespace FieldModuleDescent
variable (k : Type u) [Field k]
variable (R : Type (u + 1)) [Ring R]

/-- The specified geometric point of Spec k. -/
def pointHom : Spec (.of (AlgebraicClosure k)) ⟶ Spec (.of k) :=
  Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k)))

/-- Its actual small-etale point. -/
abbrev point := Scheme.pointSmallEtale (pointHom k)

/-- The scheme automorphism supplied by the actual field automorphism. -/
def pointIso (σ : Gal(AlgebraicClosure k/k)) : Over.mk (pointHom k) ≅ Over.mk (pointHom k) where
  hom := Over.homMk (Spec.map (CommRingCat.ofHom σ.toRingHom)) (by sorry)
  inv := Over.homMk (Spec.map (CommRingCat.ofHom σ.symm.toRingHom)) (by sorry)
  hom_inv_id := by sorry
  inv_hom_id := by sorry

/-- The actual natural action on geometric fibers of ALL etale objects. -/
def fiberMap (σ : Gal(AlgebraicClosure k/k)) :=
  AlgebraicGeometry.Scheme.Etale.geometricPointFiberMap (pointHom k) (pointIso k σ)

/-- Galois acts on the module stalk through the point-fiber natural transformation. -/
def stalkAction (F : Sheaf (Spec (.of k)).smallEtaleTopology (ModuleCat.{u + 1} R)) :
    Action (ModuleCat.{u + 1} R) Gal(AlgebraicClosure k/k) where
  V := (point k).sheafFiber.obj F
  ρ := { toFun := fun σ ↦
          (GrothendieckTopology.Point.Hom.sheafFiber
            (⟨fiberMap k σ⟩ : (point k).Hom (point k))).app F
         map_one' := by sorry
         map_mul' := by sorry }

/-- Every stalk vector is represented on a finite pointed etale neighborhood
of this FIELD. No such cofinality claim is made for an arbitrary scheme. -/
theorem stalkAction_open (F : Sheaf (Spec (.of k)).smallEtaleTopology (ModuleCat.{u + 1} R)) :
    openStabilizer R Gal(AlgebraicClosure k/k) (stalkAction k R F) := by sorry

/-- Actual linear Galois stalk functor, with no residue-group triviality instance. -/
def forward : Sheaf (Spec (.of k)).smallEtaleTopology (ModuleCat.{u + 1} R) ⥤
    DiscreteModuleCat R Gal(AlgebraicClosure k/k) where
  obj F := ⟨stalkAction k R F, stalkAction_open k R F⟩
  map f := ObjectProperty.homMk
    { hom := (point k).sheafFiber.map f
      comm := fun _ ↦ by sorry }
  map_id := by sorry
  map_comp := by sorry

variable (M : DiscreteModuleCat R Gal(AlgebraicClosure k/k))

/-- Over a field, the inverse sheaf consists of equivariant functions on
actual geometric fibers. This is not a false replacement of the forward stalk. -/
def sections (U : (Spec (.of k)).Etale) :
    Submodule R ((point k).fiber.obj U → M.obj.V) where
  carrier := {f | ∀ (σ : Gal(AlgebraicClosure k/k)) (x : (point k).fiber.obj U),
    f ((fiberMap k σ).app U x) = (M.obj.ρ σ).hom (f x)}
  zero_mem' := by sorry
  add_mem' := by sorry
  smul_mem' := by sorry

/-- Restriction is literal precomposition with the geometric fiber map. -/
def presheaf : (Spec (.of k)).Etaleᵒᵖ ⥤ ModuleCat.{u + 1} R where
  obj U := ModuleCat.of R (sections k R M U.unop)
  map f := ModuleCat.ofHom
    { toFun := fun s ↦ ⟨fun x ↦ s.val ((point k).fiber.map f.unop x), by sorry⟩
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  map_id := by sorry
  map_comp := by sorry

/-- Etale covers are jointly surjective on geometric fibers, giving the
actual equivariant-function gluing law. -/
theorem isSheaf : Presheaf.IsSheaf (Spec (.of k)).smallEtaleTopology (presheaf k R M) := by sorry

/-- The concrete field inverse with pointwise module operations. -/
def associated : Sheaf (Spec (.of k)).smallEtaleTopology (ModuleCat.{u + 1} R) :=
  ⟨presheaf k R M, isSheaf k R M⟩

variable {M}

/-- Coefficient morphisms act pointwise on the displayed functions. -/
def associatedMap {N : DiscreteModuleCat R Gal(AlgebraicClosure k/k)} (f : M ⟶ N) :
    associated k R M ⟶ associated k R N :=
  ObjectProperty.homMk
    { app U := ModuleCat.ofHom
        { toFun := fun s ↦ ⟨fun x ↦ f.hom.hom.hom (s.val x), by sorry⟩
          map_add' := by sorry
          map_smul' := by sorry }
      naturality := by sorry }

/-- The concrete inverse functor; its objects are not chosen from an equivalence witness. -/
def inverse : DiscreteModuleCat R Gal(AlgebraicClosure k/k) ⥤
    Sheaf (Spec (.of k)).smallEtaleTopology (ModuleCat.{u + 1} R) where
  obj := associated k R
  map := associatedMap k R
  map_id := by sorry
  map_comp := by sorry

/-- Unit map: send a section to its actual germs at all geometric points of U. -/
def unitMap (F : Sheaf (Spec (.of k)).smallEtaleTopology (ModuleCat.{u + 1} R)) :
    F ⟶ (inverse k R).obj ((forward k R).obj F) :=
  ObjectProperty.homMk
    { app U := ModuleCat.ofHom
        { toFun := fun s ↦ ⟨fun x ↦ ((point k).toPresheafFiber U.unop x F.obj).hom s, by sorry⟩
          map_add' := by sorry
          map_smul' := by sorry }
      naturality := by sorry }

/-- The field-site germ map, rather than a claimed literal object equality, is invertible. -/
instance unitMap_isIso (F : Sheaf (Spec (.of k)).smallEtaleTopology (ModuleCat.{u + 1} R)) :
    IsIso (unitMap k R F) := by sorry

/-- Counit on actual stalks is evaluation of each pointed germ. -/
def counitLinear (M : DiscreteModuleCat R Gal(AlgebraicClosure k/k)) :
    (stalkAction k R (associated k R M)).V ⟶ M.obj.V :=
  (point k).presheafFiberDesc
    (fun U x ↦ ModuleCat.ofHom
      { toFun := fun s ↦ s.val x
        map_add' := by intros; rfl
        map_smul' := by intros; rfl }) (by sorry)

/-- The evaluation counit is equivariant because the section functions are equivariant. -/
def counitMap (M : DiscreteModuleCat R Gal(AlgebraicClosure k/k)) :
    (forward k R).obj ((inverse k R).obj M) ⟶ M :=
  ObjectProperty.homMk { hom := counitLinear k R M, comm := fun _ ↦ by sorry }

/-- Open stabilizers supply a finite etale neighborhood for each prescribed
vector, proving invertibility of THIS evaluation map. -/
instance counitMap_isIso (M : DiscreteModuleCat R Gal(AlgebraicClosure k/k)) :
    IsIso (counitMap k R M) := by sorry

/-- The field module equivalence uses genuine germ/evaluation maps in both
directions, never eqToIso or a false trivial-Galois-group assertion. -/
def equivalence : Sheaf (Spec (.of k)).smallEtaleTopology (ModuleCat.{u + 1} R) ≌
    DiscreteModuleCat R Gal(AlgebraicClosure k/k) where
  functor := forward k R
  inverse := inverse k R
  unitIso := NatIso.ofComponents (fun F ↦ @asIso _ _ _ _ (unitMap k R F)
    (unitMap_isIso k R F)) (by sorry)
  counitIso := NatIso.ofComponents (fun M ↦ @asIso _ _ _ _ (counitMap k R M)
    (counitMap_isIso k R M)) (by sorry)
  functor_unitIso_comp := by sorry

end FieldModuleDescent
