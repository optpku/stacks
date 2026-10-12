/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Action.ModuleCat.OpenStabilizer.Definition
public import stacks_project.Chap59.Theorem_59_56_3_StalkFunctor

open CategoryTheory Opposite
open CategoryTheory.Action ModuleCat
open AlgebraicGeometry

@[expose] public section

universe u

noncomputable section

namespace AlgebraicGeometry.Scheme.Etale

/-- The additive geometric fiber of an abelian sheaf at the separable geometric
point associated to `s`. -/
def stalkAddCommGrp (K : Type u) [Field K] (s : GeometricPoint (Spec (.of K)))
    (F : Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u}) :
    AddCommGrpCat.{u} :=
  ((etalePoint K s).sheafFiber :
      Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u} ⥤
        AddCommGrpCat.{u}).obj F

/-- Compatibility of Galois-twisted generator maps with restriction, used to
descend the action to the additive stalk. -/
theorem stalkGaloisModuleAction_compatible (K : Type u) [Field K]
    (s : GeometricPoint (Spec (.of K)))
    (F : Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u})
    (σ : s.absoluteGaloisGroup) :
    ∀ ⦃U V : (Spec (.of K)).Etale⦄ (f : U ⟶ V)
      (x : (etalePoint K s).fiber.obj U),
      F.obj.map f.op ≫
          (etalePoint K s).toPresheafFiber U
            ((geometricPointFiberMap (geometricPointHom K s)
                (geometricPointGaloisIso K s σ)).app U x) F.obj =
        (etalePoint K s).toPresheafFiber V
          ((geometricPointFiberMap (geometricPointHom K s)
              (geometricPointGaloisIso K s σ)).app V
            ((etalePoint K s).fiber.map f x)) F.obj :=
  sorry

/-- The additive endomorphism of the étale stalk induced by a Galois
automorphism of `κ(s)^sep`. -/
def stalkGaloisModuleAction (K : Type u) [Field K]
    (s : GeometricPoint (Spec (.of K)))
    (F : Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u})
    (σ : s.absoluteGaloisGroup) :
    stalkAddCommGrp K s F ⟶ stalkAddCommGrp K s F :=
  (etalePoint K s).presheafFiberDesc
    (fun U x ↦
      (etalePoint K s).toPresheafFiber U
        ((geometricPointFiberMap (geometricPointHom K s)
            (geometricPointGaloisIso K s σ)).app U x) F.obj)
    (stalkGaloisModuleAction_compatible K s F σ)

/-- The discrete continuous `Gal_κ(s)`-module obtained as the étale stalk of an
abelian sheaf at the geometric point determined by `κ(s)^sep`. -/
def stalkGaloisModuleObj (K : Type u) [Field K]
    (s : GeometricPoint (Spec (.of K)))
    (F : Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u}) :
    DiscreteModuleCat ℤ s.absoluteGaloisGroup :=
  let V := ModuleCat.of ℤ (stalkAddCommGrp K s F)
  let rho : s.absoluteGaloisGroup →* End V :=
    { toFun := fun σ ↦ ModuleCat.ofHom
        (stalkGaloisModuleAction K s F σ).hom.toIntLinearMap
      map_one' := sorry
      map_mul' := sorry }
  ⟨{ V := V, ρ := rho }, sorry⟩

/-- Taking étale stalks `F ↦ F_s̄` as a functor from abelian sheaves on the
small étale site of `Spec K` to discrete continuous `Gal_κ(s)`-modules. -/
def stalkGaloisModule (K : Type u) [Field K]
    (s : GeometricPoint (Spec (.of K))) :
    Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u} ⥤
      DiscreteModuleCat ℤ s.absoluteGaloisGroup where
  obj := stalkGaloisModuleObj K s
  map {F G} f :=
    ObjectProperty.homMk
      { hom := ModuleCat.ofHom
          (((etalePoint K s).sheafFiber :
                Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u} ⥤
                  AddCommGrpCat.{u}).map f).hom.toIntLinearMap
        comm := sorry }
  map_id := sorry
  map_comp := sorry

/-- The underlying `ℤ`-module of `stalkGaloisModule` is the additive étale
stalk at the separable geometric point associated to `s`. -/
theorem stalkGaloisModule_obj_carrier (K : Type u) [Field K]
    (s : GeometricPoint (Spec (.of K)))
    (F : Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u}) :
    ((stalkGaloisModule K s).obj F).obj.V =
      ModuleCat.of ℤ (stalkAddCommGrp K s F) :=
  sorry

/-- The Galois action on an additive stalk is induced by the automorphism of
the geometric point as in `59.56.0.1`. -/
theorem stalkGaloisModule_smul (K : Type u) [Field K]
    (s : GeometricPoint (Spec (.of K)))
    (F : Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u})
    (σ : s.absoluteGaloisGroup) :
    ((stalkGaloisModule K s).obj F).obj.ρ σ =
      ModuleCat.ofHom (stalkGaloisModuleAction K s F σ).hom.toIntLinearMap :=
  sorry

end AlgebraicGeometry.Scheme.Etale

end
