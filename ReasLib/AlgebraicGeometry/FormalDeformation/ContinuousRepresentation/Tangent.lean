module

public import ReasLib.AlgebraicGeometry.FormalDeformation.ContinuousRepresentation.DualNumber
public import ReasLib.CategoryTheory.Action.ModuleCat.OpenStabilizer.LowDegree
public import ReasLib.AlgebraicGeometry.FormalDeformation.ContinuousRepresentation.RimSchlessinger
public import ReasLib.AlgebraicGeometry.FormalDeformation.RimSchlessinger.Schlessinger
public import ReasLib.AlgebraicGeometry.FormalDeformation.TangentSpace.At
public import ReasLib.RepresentationTheory.Homological.ContCohomology.FiniteDimensional
public import ReasLib.CategoryTheory.Fibered.Fiber.Isomorphism
public import Mathlib.RepresentationTheory.Invariants
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExtClass

/-!
# Continuous representation deformations over the dual numbers

The framed dual-number extension defines a connecting class in continuous first cohomology.
Invariant endomorphisms act on the trivial lift by the maps `id + εψ`.
-/

@[expose] public section

noncomputable section

open CategoryTheory Functor
open CategoryTheory.Action.ModuleCat
open CategoryTheory.Action.ModuleCat.DiscreteModuleCat
open scoped DualNumber ChangeOfRings

universe u

namespace ContinuousRep

variable (Γ Λ k : Type u) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
  [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k] [Module.Finite Λ k]
variable {V : Type u} [AddCommGroup V] [Module k V] [FiniteDimensional k V]

/-- The ordinary linear representation underlying a residue representation. -/
def residueRepresentation (ρ0 : Γ →* LinearMap.GeneralLinearGroup k V)
    (hρ0 : IsContinuousDiscrete ρ0) : Representation k Γ V :=
  toRepresentation (ofResidue Γ Λ k ρ0 hρ0)

/-- The residue representation is the endomorphism-valued view of its general-linear action. -/
theorem residueRepresentation_eq (ρ0 : Γ →* LinearMap.GeneralLinearGroup k V)
    (hρ0 : IsContinuousDiscrete ρ0) :
    residueRepresentation Γ Λ k ρ0 hρ0 = toRepresentation (ofResidue Γ Λ k ρ0 hρ0) := rfl

/-- The conjugation action on the endomorphisms of a residue representation. -/
def endRepresentation (ρ0 : Γ →* LinearMap.GeneralLinearGroup k V)
    (hρ0 : IsContinuousDiscrete ρ0) : Representation k Γ (Module.End k V) :=
  Representation.linHom (residueRepresentation Γ Λ k ρ0 hρ0)
    (residueRepresentation Γ Λ k ρ0 hρ0)

/-- The action on an endomorphism is conjugation by the residue action. -/
theorem endRepresentation_apply (ρ0 : Γ →* LinearMap.GeneralLinearGroup k V)
    (hρ0 : IsContinuousDiscrete ρ0) (γ : Γ) (ψ : Module.End k V) :
    endRepresentation Γ Λ k ρ0 hρ0 γ ψ =
      residueRepresentation Γ Λ k ρ0 hρ0 γ ∘ₗ ψ ∘ₗ
        residueRepresentation Γ Λ k ρ0 hρ0 γ⁻¹ := rfl

/-- Invariant endomorphisms are precisely the endomorphisms commuting with the action. -/
theorem mem_endRepresentation_invariants_iff
    (ρ0 : Γ →* LinearMap.GeneralLinearGroup k V) (hρ0 : IsContinuousDiscrete ρ0)
    (ψ : Module.End k V) :
    ψ ∈ (endRepresentation Γ Λ k ρ0 hρ0).invariants ↔
      ∀ γ : Γ, ψ ∘ₗ (ρ0 γ).val = (ρ0 γ).val ∘ₗ ψ := by
  change (∀ γ, residueRepresentation Γ Λ k ρ0 hρ0 γ ∘ₗ ψ ∘ₗ
    residueRepresentation Γ Λ k ρ0 hρ0 γ⁻¹ = ψ) ↔ _
  rw [Representation.mem_linHom_invariants_iff_isIntertwining]
  constructor
  · intro h γ
    exact LinearMap.ext (h.isIntertwining γ)
  · intro h
    exact ⟨fun γ v ↦ LinearMap.congr_fun (h γ) v⟩

/-- The conjugation action has open point stabilizers. -/
theorem endDiscreteModule_openStabilizer
    (ρ0 : Γ →* LinearMap.GeneralLinearGroup k V) (hρ0 : IsContinuousDiscrete ρ0) :
    openStabilizer k Γ
      ((Rep.RepToAction k Γ).obj (Rep.of (endRepresentation Γ Λ k ρ0 hρ0))) := by
  sorry

/-- The discrete continuous coefficient module of endomorphisms with the conjugation action. -/
def endDiscreteModule (ρ0 : Γ →* LinearMap.GeneralLinearGroup k V)
    (hρ0 : IsContinuousDiscrete ρ0) : DiscreteModuleCat k Γ :=
  ⟨(Rep.RepToAction k Γ).obj (Rep.of (endRepresentation Γ Λ k ρ0 hρ0)),
    endDiscreteModule_openStabilizer Γ Λ k ρ0 hρ0⟩

/-- The underlying action of the endomorphism coefficient is the conjugation representation. -/
theorem endDiscreteModule_obj (ρ0 : Γ →* LinearMap.GeneralLinearGroup k V)
    (hρ0 : IsContinuousDiscrete ρ0) :
    (endDiscreteModule Γ Λ k ρ0 hρ0).obj =
      (Rep.RepToAction k Γ).obj (Rep.of (endRepresentation Γ Λ k ρ0 hρ0)) := rfl

/-- The conjugation coefficient of a finite-dimensional representation is finite-dimensional. -/
instance instFiniteDimensionalEndDiscreteModule
    (ρ0 : Γ →* LinearMap.GeneralLinearGroup k V) (hρ0 : IsContinuousDiscrete ρ0) :
    FiniteDimensional k (endDiscreteModule Γ Λ k ρ0 hρ0).obj.V := by
  change FiniteDimensional k (Module.End k V)
  infer_instance

/-- The linear endomorphism `id + εψ` on the scalar-extended module. -/
def idAddEps (ψ : Module.End k V) :
    Module.End (ArtinianLocalAlgCat.dualNumber Λ k).carrier (trivialModule Λ k V) :=
  let epsilon : (ArtinianLocalAlgCat.dualNumber Λ k).carrier := DualNumber.eps
  LinearMap.id + epsilon • extendEnd Λ k V ψ

/-- The perturbation of the identity is the sum of the identity and the scalar-extended map
multiplied by the dual-number generator. -/
theorem idAddEps_def (ψ : Module.End k V) :
    idAddEps Λ k ψ =
      (let epsilon : (ArtinianLocalAlgCat.dualNumber Λ k).carrier := DualNumber.eps
       LinearMap.id + epsilon • extendEnd Λ k V ψ) := rfl

/-- An invariant endomorphism induces an equivariant perturbation of the identity. -/
theorem idAddEps_equivariant (ρ0 : Γ →* LinearMap.GeneralLinearGroup k V)
    (hρ0 : IsContinuousDiscrete ρ0)
    (ψ : (endRepresentation Γ Λ k ρ0 hρ0).invariants)
    (γ : Γ) (m : trivialModule Λ k V) :
    idAddEps Λ k ψ.val ((trivialRho Γ Λ k ρ0 γ).val m) =
      (trivialRho Γ Λ k ρ0 γ).val (idAddEps Λ k ψ.val m) := by
  sorry

/-- The perturbations `id + εψ` and `id − εψ` are inverse linear maps. -/
theorem idAddEps_comp_neg (ψ : Module.End k V) :
    idAddEps Λ k (-ψ) ∘ₗ idAddEps Λ k ψ = LinearMap.id := by
  sorry

/-- A perturbation of the identity by the dual-number generator induces a base-change
isomorphism over the identity of the coefficient ring. -/
theorem idAddEps_isBaseChange
    (ρ0 : Γ →* LinearMap.GeneralLinearGroup k V) (hρ0 : IsContinuousDiscrete ρ0)
    (ψ : Module.End k V) :
    IsBaseChangeAlong (X := trivialDeformationObj Γ Λ k ρ0 hρ0)
      (Y := trivialDeformationObj Γ Λ k ρ0 hρ0) (𝟙 _)
      (fun m ↦ idAddEps Λ k ψ m)
      (by intro a b; exact (idAddEps Λ k ψ).map_add a b)
      (by intro a m; exact (idAddEps Λ k ψ).map_smul a m) := by
  sorry

private theorem hom_ext {X Y : ContinuousRep Γ Λ k} {f g : X ⟶ Y}
    (hb : f.base = g.base) (hf : f.toFun = g.toFun) : f = g := by
  rcases f with ⟨fb, ff, fa, fs, fe, fi⟩
  rcases g with ⟨gb, gf, ga, gs, ge, gi⟩
  change fb = gb at hb
  cases hb
  change ff = gf at hf
  cases hf
  rfl

/-- The representation automorphism whose forward map is `id + εψ` and whose inverse map
is `id − εψ`. -/
def idAddEpsIso (ρ0 : Γ →* LinearMap.GeneralLinearGroup k V)
    (hρ0 : IsContinuousDiscrete ρ0)
    (ψ : (endRepresentation Γ Λ k ρ0 hρ0).invariants) :
    trivialDeformationObj Γ Λ k ρ0 hρ0 ≅ trivialDeformationObj Γ Λ k ρ0 hρ0 where
  hom := Hom.of (𝟙 _)
    (fun m ↦ idAddEps Λ k ψ.val m)
    (by intro a b; exact (idAddEps Λ k ψ.val).map_add a b)
    (by intro a m; exact (idAddEps Λ k ψ.val).map_smul a m)
    (idAddEps_equivariant Γ Λ k ρ0 hρ0 ψ)
    (idAddEps_isBaseChange Γ Λ k ρ0 hρ0 ψ.val)
  inv := Hom.of (𝟙 _)
    (fun m ↦ idAddEps Λ k (-ψ).val m)
    (by intro a b; exact (idAddEps Λ k (-ψ).val).map_add a b)
    (by intro a m; exact (idAddEps Λ k (-ψ).val).map_smul a m)
    (idAddEps_equivariant Γ Λ k ρ0 hρ0 (-ψ))
    (idAddEps_isBaseChange Γ Λ k ρ0 hρ0 (-ψ).val)
  hom_inv_id := by
    apply hom_ext Γ Λ k
    · exact Category.id_comp _
    · funext m
      exact LinearMap.congr_fun (idAddEps_comp_neg Λ k ψ.val) m
  inv_hom_id := by
    apply hom_ext Γ Λ k
    · exact Category.id_comp _
    · funext m
      change idAddEps Λ k ψ.val (idAddEps Λ k (-ψ.val) m) = m
      simpa only [neg_neg, LinearMap.comp_apply, LinearMap.id_apply] using
        LinearMap.congr_fun (idAddEps_comp_neg Λ k (-ψ.val)) m

/-- The forward map of the representation automorphism is `id + εψ`. -/
theorem idAddEpsIso_hom (ρ0 : Γ →* LinearMap.GeneralLinearGroup k V)
    (hρ0 : IsContinuousDiscrete ρ0)
    (ψ : (endRepresentation Γ Λ k ρ0 hρ0).invariants) :
    (idAddEpsIso Γ Λ k ρ0 hρ0 ψ).hom.toFun = fun m ↦ idAddEps Λ k ψ.val m := rfl

private theorem idAddEpsIso_vertical (ρ0 : Γ →* LinearMap.GeneralLinearGroup k V)
    (hρ0 : IsContinuousDiscrete ρ0)
    (ψ : (endRepresentation Γ Λ k ρ0 hρ0).invariants) :
    (forget Γ Λ k).IsHomLift (𝟙 (ArtinianLocalAlgCat.dualNumber Λ k))
      (idAddEpsIso Γ Λ k ρ0 hρ0 ψ).hom := by
  exact IsHomLift.of_fac (forget Γ Λ k) _ _ rfl rfl rfl

/-- An invariant perturbation of the identity fixes the retraction to the residue object. -/
theorem idAddEpsIso_infinitesimal
    (ρ0 : Γ →* LinearMap.GeneralLinearGroup k V) (hρ0 : IsContinuousDiscrete ρ0)
    (ψ : (endRepresentation Γ Λ k ρ0 hρ0).invariants) :
    Fiber.isoMk (idAddEpsIso Γ Λ k ρ0 hρ0 ψ)
        (by exact idAddEpsIso_vertical Γ Λ k ρ0 hρ0 ψ) ∈
      infinitesimalAutomorphismsAt (forget Γ Λ k) (residueObj Γ Λ k ρ0 hρ0)
        (trivialDeformation Γ Λ k ρ0 hρ0) (trivialPushforward Γ Λ k ρ0 hρ0) := by
  sorry

/-- The infinitesimal automorphism associated to an invariant endomorphism by `ψ ↦ id + εψ`. -/
def infAutOfInvariants (ρ0 : Γ →* LinearMap.GeneralLinearGroup k V)
    (hρ0 : IsContinuousDiscrete ρ0) (ψ : (endRepresentation Γ Λ k ρ0 hρ0).invariants) :
    infinitesimalAutomorphismsAt (forget Γ Λ k) (residueObj Γ Λ k ρ0 hρ0)
      (trivialDeformation Γ Λ k ρ0 hρ0) (trivialPushforward Γ Λ k ρ0 hρ0) :=
  ⟨Fiber.isoMk (idAddEpsIso Γ Λ k ρ0 hρ0 ψ)
    (by exact idAddEpsIso_vertical Γ Λ k ρ0 hρ0 ψ),
    idAddEpsIso_infinitesimal Γ Λ k ρ0 hρ0 ψ⟩

/-- The underlying module map of the associated infinitesimal automorphism is `id + εψ`. -/
theorem infAutOfInvariants_spec (ρ0 : Γ →* LinearMap.GeneralLinearGroup k V)
    (hρ0 : IsContinuousDiscrete ρ0) (ψ : (endRepresentation Γ Λ k ρ0 hρ0).invariants) :
    (Fiber.fiberInclusion.map (infAutOfInvariants Γ Λ k ρ0 hρ0 ψ).val.hom).toFun =
      fun m ↦ idAddEps Λ k ψ.val m := rfl

/-- Addition of invariant endomorphisms corresponds to composition of infinitesimal
representation automorphisms. -/
theorem infAutOfInvariants_map_add (ρ0 : Γ →* LinearMap.GeneralLinearGroup k V)
    (hρ0 : IsContinuousDiscrete ρ0)
    (ψ φ : (endRepresentation Γ Λ k ρ0 hρ0).invariants) :
    infAutOfInvariants Γ Λ k ρ0 hρ0 (ψ + φ) =
      infAutOfInvariants Γ Λ k ρ0 hρ0 ψ * infAutOfInvariants Γ Λ k ρ0 hρ0 φ := by
  sorry

/-- Every infinitesimal representation automorphism is uniquely a perturbation by an
invariant endomorphism. -/
theorem infAutOfInvariants_bijective (ρ0 : Γ →* LinearMap.GeneralLinearGroup k V)
    (hρ0 : IsContinuousDiscrete ρ0) :
    Function.Bijective (infAutOfInvariants Γ Λ k ρ0 hρ0) := by
  sorry


-- Module visibility justification: private extension constructions occur in the body of
-- the public connecting class, so Lean must retain their implementations on export.
set_option backward.privateInPublic true

private def liftScalarMap
    (ρ0 : Γ →* LinearMap.GeneralLinearGroup k V) (hρ0 : IsContinuousDiscrete ρ0)
    (x : { y : Over (ofResidue Γ Λ k ρ0 hρ0) // y.left.base = ArtinianLocalAlgCat.dualNumber Λ k }) :
    k →+* x.val.left.base.carrier :=
  ((ArtinianLocalAlgCat.residueToDualNumber Λ k) ≫ eqToHom x.property.symm).hom.toRingHom

private def liftModule
    (ρ0 : Γ →* LinearMap.GeneralLinearGroup k V) (hρ0 : IsContinuousDiscrete ρ0)
    (x : { y : Over (ofResidue Γ Λ k ρ0 hρ0) // y.left.base = ArtinianLocalAlgCat.dualNumber Λ k }) :
    ModuleCat k :=
  (ModuleCat.restrictScalars (liftScalarMap Γ Λ k ρ0 hρ0 x)).obj x.val.left.module

private def liftScalarEnd
    (ρ0 : Γ →* LinearMap.GeneralLinearGroup k V) (hρ0 : IsContinuousDiscrete ρ0)
    (x : { y : Over (ofResidue Γ Λ k ρ0 hρ0) // y.left.base = ArtinianLocalAlgCat.dualNumber Λ k })
    (a : x.val.left.base.carrier) :
    Module.End k (liftModule Γ Λ k ρ0 hρ0 x) :=
  ((ModuleCat.restrictScalars (liftScalarMap Γ Λ k ρ0 hρ0 x)).map
    (ModuleCat.ofHom (a • (LinearMap.id : Module.End x.val.left.base.carrier
      x.val.left.module)))).hom

private def liftEps
    (ρ0 : Γ →* LinearMap.GeneralLinearGroup k V) (hρ0 : IsContinuousDiscrete ρ0)
    (x : { y : Over (ofResidue Γ Λ k ρ0 hρ0) // y.left.base = ArtinianLocalAlgCat.dualNumber Λ k }) :
    Module.End k (liftModule Γ Λ k ρ0 hρ0 x) :=
  liftScalarEnd Γ Λ k ρ0 hρ0 x
    ((eqToHom x.property.symm : ArtinianLocalAlgCat.dualNumber Λ k ⟶ x.val.left.base).hom
      DualNumber.eps)

private def liftRepresentation
    (ρ0 : Γ →* LinearMap.GeneralLinearGroup k V) (hρ0 : IsContinuousDiscrete ρ0)
    (x : { y : Over (ofResidue Γ Λ k ρ0 hρ0) // y.left.base = ArtinianLocalAlgCat.dualNumber Λ k }) :
    Representation k Γ (liftModule Γ Λ k ρ0 hρ0 x) :=
  ((Rep.ActionToRep k Γ).obj
    (((ModuleCat.restrictScalars (liftScalarMap Γ Λ k ρ0 hρ0 x)).mapAction Γ).obj
      ((Rep.RepToAction x.val.left.base.carrier Γ).obj
        (Rep.of (toRepresentation x.val.left))))).ρ

private def residueScalarMap
    (ρ0 : Γ →* LinearMap.GeneralLinearGroup k V) (hρ0 : IsContinuousDiscrete ρ0)
    (x : { y : Over (ofResidue Γ Λ k ρ0 hρ0) // y.left.base = ArtinianLocalAlgCat.dualNumber Λ k }) :
    x.val.left.base.carrier →+* k := x.val.hom.base.hom.toRingHom

private def liftFraming
    (ρ0 : Γ →* LinearMap.GeneralLinearGroup k V) (hρ0 : IsContinuousDiscrete ρ0)
    (x : { y : Over (ofResidue Γ Λ k ρ0 hρ0) // y.left.base = ArtinianLocalAlgCat.dualNumber Λ k }) :
    liftModule Γ Λ k ρ0 hρ0 x → V := x.val.hom.toFun

private theorem dualNumberReduction_laws
    (ρ0 : Γ →* LinearMap.GeneralLinearGroup k V) (hρ0 : IsContinuousDiscrete ρ0)
    (x : { y : Over (ofResidue Γ Λ k ρ0 hρ0) // y.left.base = ArtinianLocalAlgCat.dualNumber Λ k }) :
    (∀ (a : k) (m : liftModule Γ Λ k ρ0 hρ0 x),
      liftFraming Γ Λ k ρ0 hρ0 x (a • m) = a • liftFraming Γ Λ k ρ0 hρ0 x m) ∧
    (∀ (r : x.val.left.base.carrier) (a : k) (m : liftModule Γ Λ k ρ0 hρ0 x),
      (residueScalarMap Γ Λ k ρ0 hρ0 x r * a) • liftEps Γ Λ k ρ0 hρ0 x m =
        a • liftEps Γ Λ k ρ0 hρ0 x (liftScalarEnd Γ Λ k ρ0 hρ0 x r m)) ∧
    Function.Surjective (liftFraming Γ Λ k ρ0 hρ0 x) := by
  sorry

private def dualNumberReduction
    (ρ0 : Γ →* LinearMap.GeneralLinearGroup k V) (hρ0 : IsContinuousDiscrete ρ0)
    (x : { y : Over (ofResidue Γ Λ k ρ0 hρ0) // y.left.base = ArtinianLocalAlgCat.dualNumber Λ k }) :
    liftModule Γ Λ k ρ0 hρ0 x →ₗ[k] V where
  toFun := liftFraming Γ Λ k ρ0 hρ0 x
  map_add' := by intro a b; exact x.val.hom.map_add a b
  map_smul' := (dualNumberReduction_laws Γ Λ k ρ0 hρ0 x).1

private def residueBaseChange
    (ρ0 : Γ →* LinearMap.GeneralLinearGroup k V) (hρ0 : IsContinuousDiscrete ρ0)
    (x : { y : Over (ofResidue Γ Λ k ρ0 hρ0) // y.left.base = ArtinianLocalAlgCat.dualNumber Λ k }) :
    ModuleCat k :=
  (ModuleCat.extendScalars (residueScalarMap Γ Λ k ρ0 hρ0 x)).obj x.val.left.module

private def residueBaseChangeIso
    (ρ0 : Γ →* LinearMap.GeneralLinearGroup k V) (hρ0 : IsContinuousDiscrete ρ0)
    (x : { y : Over (ofResidue Γ Λ k ρ0 hρ0) // y.left.base = ArtinianLocalAlgCat.dualNumber Λ k }) :
    residueBaseChange Γ Λ k ρ0 hρ0 x ≅ ModuleCat.of k V :=
  @asIso (ModuleCat k) _ _ _
    (inducedAlong x.val.hom.base x.val.hom.toFun x.val.hom.map_add x.val.hom.map_smul)
    x.val.hom.isBaseChange

private def epsilonPair
    (ρ0 : Γ →* LinearMap.GeneralLinearGroup k V) (hρ0 : IsContinuousDiscrete ρ0)
    (x : { y : Over (ofResidue Γ Λ k ρ0 hρ0) // y.left.base = ArtinianLocalAlgCat.dualNumber Λ k }) :
    k →+ x.val.left.module →+ liftModule Γ Λ k ρ0 hρ0 x where
  toFun a :=
    { toFun := fun m ↦ a • liftEps Γ Λ k ρ0 hρ0 x m
      map_zero' := by
        exact (congrArg (fun m : liftModule Γ Λ k ρ0 hρ0 x ↦ a • m)
          (liftEps Γ Λ k ρ0 hρ0 x).map_zero).trans (smul_zero a)
      map_add' := by
        intro m n
        exact (congrArg (fun v : liftModule Γ Λ k ρ0 hρ0 x ↦ a • v)
          ((liftEps Γ Λ k ρ0 hρ0 x).map_add m n)).trans (smul_add a _ _) }
  map_zero' := by ext m; exact zero_smul k _
  map_add' := by intro a b; ext m; exact add_smul a b _

private def epsilonDescendAdd
    (ρ0 : Γ →* LinearMap.GeneralLinearGroup k V) (hρ0 : IsContinuousDiscrete ρ0)
    (x : { y : Over (ofResidue Γ Λ k ρ0 hρ0) // y.left.base = ArtinianLocalAlgCat.dualNumber Λ k }) :
    residueBaseChange Γ Λ k ρ0 hρ0 x →+ liftModule Γ Λ k ρ0 hρ0 x :=
  TensorProduct.liftAddHom (R := x.val.left.base.carrier)
    (M := (ModuleCat.restrictScalars (residueScalarMap Γ Λ k ρ0 hρ0 x)).obj (ModuleCat.of k k))
    (epsilonPair Γ Λ k ρ0 hρ0 x)
    (by intro r a m; exact (dualNumberReduction_laws Γ Λ k ρ0 hρ0 x).2.1 r a m)

private def epsilonDescend
    (ρ0 : Γ →* LinearMap.GeneralLinearGroup k V) (hρ0 : IsContinuousDiscrete ρ0)
    (x : { y : Over (ofResidue Γ Λ k ρ0 hρ0) // y.left.base = ArtinianLocalAlgCat.dualNumber Λ k }) :
    residueBaseChange Γ Λ k ρ0 hρ0 x →ₗ[k] liftModule Γ Λ k ρ0 hρ0 x where
  toFun := epsilonDescendAdd Γ Λ k ρ0 hρ0 x
  map_add' := (epsilonDescendAdd Γ Λ k ρ0 hρ0 x).map_add
  map_smul' a t := by
    induction t using TensorProduct.induction_on with
    | zero =>
      have hzero : a • (0 : residueBaseChange Γ Λ k ρ0 hρ0 x) = 0 := smul_zero a
      have hleft := (congrArg (epsilonDescendAdd Γ Λ k ρ0 hρ0 x) hzero).trans
        (epsilonDescendAdd Γ Λ k ρ0 hρ0 x).map_zero
      have hright := (congrArg (fun m : liftModule Γ Λ k ρ0 hρ0 x ↦ a • m)
        (epsilonDescendAdd Γ Λ k ρ0 hρ0 x).map_zero).trans (smul_zero a)
      exact hleft.trans hright.symm
    | tmul b m =>
      change k at b
      change (a * b) • liftEps Γ Λ k ρ0 hρ0 x m =
        a • (b • liftEps Γ Λ k ρ0 hρ0 x m)
      exact mul_smul a b _
    | add t t' ht ht' =>
      change residueBaseChange Γ Λ k ρ0 hρ0 x at t t'
      have hsum : a • ((t : residueBaseChange Γ Λ k ρ0 hρ0 x) + t') = a • t + a • t' :=
        smul_add a t t'
      calc
        (epsilonDescendAdd Γ Λ k ρ0 hρ0 x) (a • (t + t')) =
            (epsilonDescendAdd Γ Λ k ρ0 hρ0 x) (a • t) +
              (epsilonDescendAdd Γ Λ k ρ0 hρ0 x) (a • t') :=
          (congrArg (epsilonDescendAdd Γ Λ k ρ0 hρ0 x) hsum).trans
            ((epsilonDescendAdd Γ Λ k ρ0 hρ0 x).map_add _ _)
        _ = a • (epsilonDescendAdd Γ Λ k ρ0 hρ0 x) t +
              a • (epsilonDescendAdd Γ Λ k ρ0 hρ0 x) t' := congrArg₂ (· + ·) ht ht'
        _ = a • (epsilonDescendAdd Γ Λ k ρ0 hρ0 x) (t + t') :=
          (smul_add a _ _).symm.trans
            (congrArg (fun m : liftModule Γ Λ k ρ0 hρ0 x ↦ a • m)
              ((epsilonDescendAdd Γ Λ k ρ0 hρ0 x).map_add t t').symm)

private def dualNumberKernelIncl
    (ρ0 : Γ →* LinearMap.GeneralLinearGroup k V) (hρ0 : IsContinuousDiscrete ρ0)
    (x : { y : Over (ofResidue Γ Λ k ρ0 hρ0) // y.left.base = ArtinianLocalAlgCat.dualNumber Λ k }) :
    V →ₗ[k] liftModule Γ Λ k ρ0 hρ0 x :=
  (epsilonDescend Γ Λ k ρ0 hρ0 x).comp (residueBaseChangeIso Γ Λ k ρ0 hρ0 x).inv.hom

private theorem dualNumberKernelIncl_laws
    (ρ0 : Γ →* LinearMap.GeneralLinearGroup k V) (hρ0 : IsContinuousDiscrete ρ0)
    (x : { y : Over (ofResidue Γ Λ k ρ0 hρ0) // y.left.base = ArtinianLocalAlgCat.dualNumber Λ k }) :
    (∀ m, dualNumberKernelIncl Γ Λ k ρ0 hρ0 x
      (dualNumberReduction Γ Λ k ρ0 hρ0 x m) = liftEps Γ Λ k ρ0 hρ0 x m) ∧
    Function.Injective (dualNumberKernelIncl Γ Λ k ρ0 hρ0 x) ∧
    (dualNumberReduction Γ Λ k ρ0 hρ0 x).comp
      (dualNumberKernelIncl Γ Λ k ρ0 hρ0 x) = 0 ∧
    LinearMap.range (dualNumberKernelIncl Γ Λ k ρ0 hρ0 x) =
      LinearMap.ker (dualNumberReduction Γ Λ k ρ0 hρ0 x) := by
  sorry

private theorem dualNumberHomCoefficients_openStabilizer
    (ρ0 : Γ →* LinearMap.GeneralLinearGroup k V) (hρ0 : IsContinuousDiscrete ρ0)
    (x : { y : Over (ofResidue Γ Λ k ρ0 hρ0) // y.left.base = ArtinianLocalAlgCat.dualNumber Λ k }) :
    openStabilizer k Γ ((Rep.RepToAction k Γ).obj
      (Rep.of (Representation.linHom (residueRepresentation Γ Λ k ρ0 hρ0)
        (liftRepresentation Γ Λ k ρ0 hρ0 x)))) := by
  sorry

private def dualNumberHomCoefficients
    (ρ0 : Γ →* LinearMap.GeneralLinearGroup k V) (hρ0 : IsContinuousDiscrete ρ0)
    (x : { y : Over (ofResidue Γ Λ k ρ0 hρ0) // y.left.base = ArtinianLocalAlgCat.dualNumber Λ k }) :
    DiscreteModuleCat k Γ :=
  ⟨(Rep.RepToAction k Γ).obj
    (Rep.of (Representation.linHom (residueRepresentation Γ Λ k ρ0 hρ0)
      (liftRepresentation Γ Λ k ρ0 hρ0 x))),
    dualNumberHomCoefficients_openStabilizer Γ Λ k ρ0 hρ0 x⟩

private theorem dualNumberHomMaps_equivariant
    (ρ0 : Γ →* LinearMap.GeneralLinearGroup k V) (hρ0 : IsContinuousDiscrete ρ0)
    (x : { y : Over (ofResidue Γ Λ k ρ0 hρ0) // y.left.base = ArtinianLocalAlgCat.dualNumber Λ k }) :
    (∀ (γ : Γ) (f : Module.End k V),
      Representation.linHom (residueRepresentation Γ Λ k ρ0 hρ0)
        (liftRepresentation Γ Λ k ρ0 hρ0 x) γ
          ((dualNumberKernelIncl Γ Λ k ρ0 hρ0 x).comp f) =
      (dualNumberKernelIncl Γ Λ k ρ0 hρ0 x).comp
        (endRepresentation Γ Λ k ρ0 hρ0 γ f)) ∧
    (∀ (γ : Γ) (f : V →ₗ[k] liftModule Γ Λ k ρ0 hρ0 x),
      endRepresentation Γ Λ k ρ0 hρ0 γ
        ((dualNumberReduction Γ Λ k ρ0 hρ0 x).comp f) =
      (dualNumberReduction Γ Λ k ρ0 hρ0 x).comp
        (Representation.linHom (residueRepresentation Γ Λ k ρ0 hρ0)
          (liftRepresentation Γ Λ k ρ0 hρ0 x) γ f)) := by
  sorry

private def dualNumberHomIncl
    (ρ0 : Γ →* LinearMap.GeneralLinearGroup k V) (hρ0 : IsContinuousDiscrete ρ0)
    (x : { y : Over (ofResidue Γ Λ k ρ0 hρ0) // y.left.base = ArtinianLocalAlgCat.dualNumber Λ k }) :
    endDiscreteModule Γ Λ k ρ0 hρ0 ⟶ dualNumberHomCoefficients Γ Λ k ρ0 hρ0 x :=
  ObjectProperty.homMk
    { hom := ModuleCat.ofHom
        { toFun := fun f ↦ (dualNumberKernelIncl Γ Λ k ρ0 hρ0 x).comp f
          map_add' := by intro f g; exact LinearMap.comp_add _ _ _
          map_smul' := by intro a f; exact LinearMap.comp_smul _ _ _ }
      comm := by
        intro γ
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro f
        exact ((dualNumberHomMaps_equivariant Γ Λ k ρ0 hρ0 x).1 γ f).symm }

private def dualNumberHomReduction
    (ρ0 : Γ →* LinearMap.GeneralLinearGroup k V) (hρ0 : IsContinuousDiscrete ρ0)
    (x : { y : Over (ofResidue Γ Λ k ρ0 hρ0) // y.left.base = ArtinianLocalAlgCat.dualNumber Λ k }) :
    dualNumberHomCoefficients Γ Λ k ρ0 hρ0 x ⟶ endDiscreteModule Γ Λ k ρ0 hρ0 :=
  ObjectProperty.homMk
    { hom := ModuleCat.ofHom
        { toFun := fun f ↦ (dualNumberReduction Γ Λ k ρ0 hρ0 x).comp f
          map_add' := by intro f g; exact LinearMap.comp_add _ _ _
          map_smul' := by intro a f; exact LinearMap.comp_smul _ _ _ }
      comm := by
        intro γ
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro f
        exact ((dualNumberHomMaps_equivariant Γ Λ k ρ0 hρ0 x).2 γ f).symm }

private def dualNumberHomComplex
    (ρ0 : Γ →* LinearMap.GeneralLinearGroup k V) (hρ0 : IsContinuousDiscrete ρ0)
    (x : { y : Over (ofResidue Γ Λ k ρ0 hρ0) // y.left.base = ArtinianLocalAlgCat.dualNumber Λ k }) :
    ShortComplex (DiscreteModuleCat k Γ) :=
  ShortComplex.mk (dualNumberHomIncl Γ Λ k ρ0 hρ0 x)
    (dualNumberHomReduction Γ Λ k ρ0 hρ0 x) (by
      apply ObjectProperty.hom_ext
      apply Action.Hom.ext
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro f
      change (dualNumberReduction Γ Λ k ρ0 hρ0 x).comp
        ((dualNumberKernelIncl Γ Λ k ρ0 hρ0 x).comp f) = 0
      rw [← LinearMap.comp_assoc, (dualNumberKernelIncl_laws Γ Λ k ρ0 hρ0 x).2.2.1]
      exact LinearMap.zero_comp _)

private theorem dualNumberHomShortExact
    (ρ0 : Γ →* LinearMap.GeneralLinearGroup k V) (hρ0 : IsContinuousDiscrete ρ0)
    (x : { y : Over (ofResidue Γ Λ k ρ0 hρ0) // y.left.base = ArtinianLocalAlgCat.dualNumber Λ k }) :
    (dualNumberHomComplex Γ Λ k ρ0 hρ0 x).ShortExact := by
  sorry

private def identityCoefficient
    (ρ0 : Γ →* LinearMap.GeneralLinearGroup k V) (hρ0 : IsContinuousDiscrete ρ0) :
    trivialCoefficient k Γ ⟶ endDiscreteModule Γ Λ k ρ0 hρ0 :=
  ObjectProperty.homMk
    { hom := ModuleCat.ofHom
        { toFun := fun a ↦ a • (LinearMap.id : Module.End k V)
          map_add' := fun a b ↦ add_smul a b _
          map_smul' := fun a b ↦ mul_smul a b _ }
      comm := by
        intro γ
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro a
        change k at a
        change a • (LinearMap.id : Module.End k V) =
          endRepresentation Γ Λ k ρ0 hρ0 γ (a • LinearMap.id)
        rw [(endRepresentation Γ Λ k ρ0 hρ0 γ).map_smul]
        congr 1
        change LinearMap.id = residueRepresentation Γ Λ k ρ0 hρ0 γ ∘ₗ
          LinearMap.id ∘ₗ residueRepresentation Γ Λ k ρ0 hρ0 γ⁻¹
        change (1 : Module.End k V) =
          (residueRepresentation Γ Λ k ρ0 hρ0 γ) *
            (residueRepresentation Γ Λ k ρ0 hρ0 γ⁻¹)
        rw [← _root_.map_mul, mul_inv_cancel, _root_.map_one] }

-- Module visibility justification: the public connecting class uses private constructions
-- of its framed extension; their implementation names are excluded from the public API.
set_option backward.privateInPublic true in
/-- The connecting class of the identity for the endomorphism sequence obtained from a framed
representation over the dual numbers. -/
def tangentClassOfLift
    (ρ0 : Γ →* LinearMap.GeneralLinearGroup k V) (hρ0 : IsContinuousDiscrete ρ0)
    (x : (deformationForget Γ Λ k ρ0 hρ0).Fiber (ArtinianLocalAlgCat.dualNumber Λ k)) :
    cohomologyObject k Γ 1 (endDiscreteModule Γ Λ k ρ0 hρ0) :=
  (Abelian.Ext.mk₀ (identityCoefficient Γ Λ k ρ0 hρ0)).comp
    (dualNumberHomShortExact Γ Λ k ρ0 hρ0 x).extClass (zero_add 1)

set_option backward.privateInPublic false

/-- Isomorphic framed representations over the dual numbers determine the same connecting
class of the identity. -/
theorem tangentClassOfLift_iso
    (ρ0 : Γ →* LinearMap.GeneralLinearGroup k V) (hρ0 : IsContinuousDiscrete ρ0)
    {x y : (deformationForget Γ Λ k ρ0 hρ0).Fiber (ArtinianLocalAlgCat.dualNumber Λ k)}
    (e : x ≅ y) :
    tangentClassOfLift Γ Λ k ρ0 hρ0 x = tangentClassOfLift Γ Λ k ρ0 hρ0 y := by
  sorry

/-- The connecting-class map from the canonical deformation tangent space to continuous first
cohomology with conjugation coefficients. -/
def tangentToH1
    (ρ0 : Γ →* LinearMap.GeneralLinearGroup k V) (hρ0 : IsContinuousDiscrete ρ0) :
    tangentSpaceAt (forget Γ Λ k) (residueObj Γ Λ k ρ0 hρ0) →
      cohomologyObject k Γ 1 (endDiscreteModule Γ Λ k ρ0 hρ0) :=
  Quotient.lift (tangentClassOfLift Γ Λ k ρ0 hρ0)
    (by intro x y h; obtain ⟨e⟩ := h; exact tangentClassOfLift_iso Γ Λ k ρ0 hρ0 e)

/-- The connecting-class map respects the canonical tangent-space vector-space operations. -/
theorem tangentToH1_isLinearMap
    (ρ0 : Γ →* LinearMap.GeneralLinearGroup k V) (hρ0 : IsContinuousDiscrete ρ0) :
    IsLinearMap k (tangentToH1 Γ Λ k ρ0 hρ0) := by
  sorry

/-- Connecting classes classify framed dual-number representation deformations up to
isomorphism. -/
theorem tangentToH1_bijective
    (ρ0 : Γ →* LinearMap.GeneralLinearGroup k V) (hρ0 : IsContinuousDiscrete ρ0) :
    Function.Bijective (tangentToH1 Γ Λ k ρ0 hρ0) := by
  sorry

/-- The canonical linear equivalence between the representation deformation tangent space and
continuous first cohomology of the conjugation representation. -/
def tangentEquivH1
    (ρ0 : Γ →* LinearMap.GeneralLinearGroup k V) (hρ0 : IsContinuousDiscrete ρ0) :
    tangentSpaceAt (forget Γ Λ k) (residueObj Γ Λ k ρ0 hρ0) ≃ₗ[k]
      cohomologyObject k Γ 1 (endDiscreteModule Γ Λ k ρ0 hρ0) :=
  LinearEquiv.ofBijective
    (IsLinearMap.mk' _ (tangentToH1_isLinearMap Γ Λ k ρ0 hρ0))
    (tangentToH1_bijective Γ Λ k ρ0 hρ0)


/-- Infinitesimal automorphisms of the trivial dual-number representation, viewed additively. -/
abbrev infinitesimalSpace
    (ρ0 : Γ →* LinearMap.GeneralLinearGroup k V) (hρ0 : IsContinuousDiscrete ρ0) :=
  Additive (infinitesimalAutomorphismsAt (forget Γ Λ k) (residueObj Γ Λ k ρ0 hρ0)
    (trivialDeformation Γ Λ k ρ0 hρ0) (trivialPushforward Γ Λ k ρ0 hρ0))

/-- The additive coordinate map from invariant endomorphisms to infinitesimal automorphisms. -/
def invariantsToInfinitesimal
    (ρ0 : Γ →* LinearMap.GeneralLinearGroup k V) (hρ0 : IsContinuousDiscrete ρ0) :
    (endRepresentation Γ Λ k ρ0 hρ0).invariants →+
      infinitesimalSpace Γ Λ k ρ0 hρ0 :=
  AddMonoidHom.mk' (fun ψ ↦ Additive.ofMul (infAutOfInvariants Γ Λ k ρ0 hρ0 ψ))
    (infAutOfInvariants_map_add Γ Λ k ρ0 hρ0)

/-- The additive equivalence between invariant endomorphisms and infinitesimal automorphisms. -/
def invariantsInfinitesimalAddEquiv
    (ρ0 : Γ →* LinearMap.GeneralLinearGroup k V) (hρ0 : IsContinuousDiscrete ρ0) :
    (endRepresentation Γ Λ k ρ0 hρ0).invariants ≃+
      infinitesimalSpace Γ Λ k ρ0 hρ0 :=
  AddEquiv.ofBijective (invariantsToInfinitesimal Γ Λ k ρ0 hρ0)
    (infAutOfInvariants_bijective Γ Λ k ρ0 hρ0)

/-- Infinitesimal representation automorphisms commute under composition. -/
instance instAddCommGroupInfinitesimalSpace
    (ρ0 : Γ →* LinearMap.GeneralLinearGroup k V) (hρ0 : IsContinuousDiscrete ρ0) :
    AddCommGroup (infinitesimalSpace Γ Λ k ρ0 hρ0) :=
  { (inferInstance : AddGroup (infinitesimalSpace Γ Λ k ρ0 hρ0)) with
    add_comm := fun a b ↦ by
      apply (invariantsInfinitesimalAddEquiv Γ Λ k ρ0 hρ0).symm.injective
      rw [_root_.map_add, _root_.map_add, add_comm] }

/-- Scalar multiplication on infinitesimal automorphisms is induced by their invariant
endomorphism coordinates and preserves the composition-defined addition. -/
instance instModuleInfinitesimalSpace
    (ρ0 : Γ →* LinearMap.GeneralLinearGroup k V) (hρ0 : IsContinuousDiscrete ρ0) :
    Module k (infinitesimalSpace Γ Λ k ρ0 hρ0) :=
  (invariantsInfinitesimalAddEquiv Γ Λ k ρ0 hρ0).symm.module k

/-- The invariant-endomorphism coordinates of infinitesimal automorphisms form a linear
equivalence. -/
def invariantsEquivInfinitesimal
    (ρ0 : Γ →* LinearMap.GeneralLinearGroup k V) (hρ0 : IsContinuousDiscrete ρ0) :
    (endRepresentation Γ Λ k ρ0 hρ0).invariants ≃ₗ[k]
      infinitesimalSpace Γ Λ k ρ0 hρ0 :=
  ((invariantsInfinitesimalAddEquiv Γ Λ k ρ0 hρ0).symm.linearEquiv k).symm

/-- The map from continuous degree-zero cohomology to actual infinitesimal automorphisms is
induced by evaluation at the unit followed by `ψ ↦ id + εψ`. -/
def h0ToInfAut
    (ρ0 : Γ →* LinearMap.GeneralLinearGroup k V) (hρ0 : IsContinuousDiscrete ρ0) :
    cohomologyObject k Γ 0 (endDiscreteModule Γ Λ k ρ0 hρ0) →
      infinitesimalAutomorphismsAt (forget Γ Λ k) (residueObj Γ Λ k ρ0 hρ0)
        (trivialDeformation Γ Λ k ρ0 hρ0) (trivialPushforward Γ Λ k ρ0 hρ0) :=
  (infAutOfInvariants Γ Λ k ρ0 hρ0) ∘
    h0EquivInvariants (endDiscreteModule Γ Λ k ρ0 hρ0)

/-- Continuous degree-zero cohomology is linearly equivalent to the additive infinitesimal
representation automorphism space. -/
def h0EquivInfinitesimal
    (ρ0 : Γ →* LinearMap.GeneralLinearGroup k V) (hρ0 : IsContinuousDiscrete ρ0) :
    cohomologyObject k Γ 0 (endDiscreteModule Γ Λ k ρ0 hρ0) ≃ₗ[k]
      infinitesimalSpace Γ Λ k ρ0 hρ0 :=
  (h0EquivInvariants (endDiscreteModule Γ Λ k ρ0 hρ0)).trans
    (invariantsEquivInfinitesimal Γ Λ k ρ0 hρ0)

/-- Infinitesimal automorphisms of a finite-dimensional continuous representation form a
finite-dimensional vector space. -/
instance instFiniteDimensionalInfinitesimalSpace
    (ρ0 : Γ →* LinearMap.GeneralLinearGroup k V) (hρ0 : IsContinuousDiscrete ρ0) :
    FiniteDimensional k (infinitesimalSpace Γ Λ k ρ0 hρ0) :=
  (invariantsEquivInfinitesimal Γ Λ k ρ0 hρ0).finiteDimensional

/-- The tangent space of a finite-dimensional continuous representation is finite-dimensional
when the topological group is topologically finitely generated. -/
theorem finiteDimensional_tangentSpaceAt
    (ρ0 : Γ →* LinearMap.GeneralLinearGroup k V) (hρ0 : IsContinuousDiscrete ρ0)
    (hΓ : TopologicalGroup.IsFinitelyGenerated Γ) :
    FiniteDimensional k (tangentSpaceAt (forget Γ Λ k) (residueObj Γ Λ k ρ0 hρ0)) := by
  exact @LinearEquiv.finiteDimensional k _ _ _ _ _ _ _
    (tangentEquivH1 Γ Λ k ρ0 hρ0).symm
    (CategoryTheory.Action.ModuleCat.DiscreteModuleCat.finiteDimensional_h1
      (endDiscreteModule Γ Λ k ρ0 hρ0) hΓ)

/-- Topological finite generation supplies canonical finite dimensionality of the actual
representation deformation tangent space. -/
instance instFiniteDimensionalTangentSpaceAt
    (ρ0 : Γ →* LinearMap.GeneralLinearGroup k V) (hρ0 : IsContinuousDiscrete ρ0)
    [Fact (TopologicalGroup.IsFinitelyGenerated Γ)] :
    FiniteDimensional k (tangentSpaceAt (forget Γ Λ k) (residueObj Γ Λ k ρ0 hρ0)) :=
  finiteDimensional_tangentSpaceAt Γ Λ k ρ0 hρ0 Fact.out

/-- The canonical connecting-class and infinitesimal-automorphism maps classify dual-number
representation deformations. The infinitesimal space is finite-dimensional, and the tangent
space is finite-dimensional for topologically finitely generated groups. -/
theorem tangent_infinitesimal_comparison
    (ρ0 : Γ →* LinearMap.GeneralLinearGroup k V) (hρ0 : IsContinuousDiscrete ρ0) :
    Function.Bijective (tangentToH1 Γ Λ k ρ0 hρ0) ∧
    Function.Bijective (h0ToInfAut Γ Λ k ρ0 hρ0) ∧
    FiniteDimensional k (infinitesimalSpace Γ Λ k ρ0 hρ0) ∧
    (TopologicalGroup.IsFinitelyGenerated Γ →
      FiniteDimensional k (tangentSpaceAt (forget Γ Λ k) (residueObj Γ Λ k ρ0 hρ0))) :=
  ⟨tangentToH1_bijective Γ Λ k ρ0 hρ0,
    (infAutOfInvariants_bijective Γ Λ k ρ0 hρ0).comp
      (h0EquivInvariants (endDiscreteModule Γ Λ k ρ0 hρ0)).bijective,
    inferInstance, finiteDimensional_tangentSpaceAt Γ Λ k ρ0 hρ0⟩

end ContinuousRep
