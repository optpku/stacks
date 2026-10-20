module

public import ReasLib.AlgebraicGeometry.FormalDeformation.GroupRepresentation.DualNumber
public import ReasLib.AlgebraicGeometry.FormalDeformation.GroupRepresentation.RimSchlessinger
public import ReasLib.AlgebraicGeometry.FormalDeformation.RimSchlessinger.Schlessinger
public import ReasLib.AlgebraicGeometry.FormalDeformation.TangentSpace.At
public import ReasLib.RepresentationTheory.Homological.GroupCohomology.Ext
public import ReasLib.RepresentationTheory.Homological.GroupCohomology.FiniteDimensional
public import ReasLib.CategoryTheory.Fibered.Fiber.Isomorphism
public import Mathlib.CategoryTheory.IsomorphismClasses
public import Mathlib.RepresentationTheory.Rep.Iso

/-!
# Tangent space and infinitesimal automorphisms of `Def_{V, ρ0}`

For a finite-dimensional residue representation, `T Def_{V, ρ0}` identifies with `Ext^1_{k[Γ]}(V, V)` and with
`H^1(Γ, End_k(V))`, while `Inf(Def_{V, ρ0})` identifies with `H^0(Γ, End_k(V))`.
-/

@[expose] public section

open CategoryTheory Functor
open scoped DualNumber

noncomputable section

universe u

namespace GroupRepCat

variable (Γ Λ k : Type u) [Group Γ] [CommRing Λ] [IsNoetherianRing Λ] [Field k]
  [Algebra Λ k] [Module.Finite Λ k]
variable {V : Type u} [AddCommGroup V] [Module k V] [Module.Finite k V]

/-- The residue representation `ρ0`, as a `k`-linear representation of `Γ` on `V`. -/
def residueRepresentation (ρ0 : Γ →* LinearMap.GeneralLinearGroup k V) :
    Representation k Γ V :=
  toRepresentation (ofResidue Γ Λ k ρ0)

/-- Unfolding of `residueRepresentation`. -/
theorem residueRepresentation_eq (ρ0 : Γ →* LinearMap.GeneralLinearGroup k V) :
    residueRepresentation Γ Λ k ρ0 = toRepresentation (ofResidue Γ Λ k ρ0) := rfl

/-- The conjugation representation of `Γ` on `End_k(V)`. -/
def endRepresentation (ρ0 : Γ →* LinearMap.GeneralLinearGroup k V) :
    Representation k Γ (Module.End k V) :=
  Representation.linHom (residueRepresentation Γ Λ k ρ0) (residueRepresentation Γ Λ k ρ0)

/-- The action of `γ` on `End_k(V)` is conjugation by `ρ0 γ`. -/
theorem endRepresentation_apply (ρ0 : Γ →* LinearMap.GeneralLinearGroup k V)
    (γ : Γ) (ψ : Module.End k V) :
    endRepresentation Γ Λ k ρ0 γ ψ =
      residueRepresentation Γ Λ k ρ0 γ ∘ₗ ψ ∘ₗ
        residueRepresentation Γ Λ k ρ0 γ⁻¹ := rfl

/-- Membership in `H^0(Γ, End_k(V))` is commutation with the action `ρ0`. -/
theorem mem_endRepresentation_invariants_iff (ρ0 : Γ →* LinearMap.GeneralLinearGroup k V)
    (ψ : Module.End k V) :
    ψ ∈ (endRepresentation Γ Λ k ρ0).invariants ↔
      ∀ γ : Γ, ψ ∘ₗ (ρ0 γ).val = (ρ0 γ).val ∘ₗ ψ := by
  change (∀ γ, (Representation.linHom (residueRepresentation Γ Λ k ρ0)
    (residueRepresentation Γ Λ k ρ0)) γ ψ = ψ) ↔ _
  exact forall_congr' (fun γ ↦ Representation.linHom.mem_invariants_iff_comm
    (X := Rep.of (residueRepresentation Γ Λ k ρ0))
    (Y := Rep.of (residueRepresentation Γ Λ k ρ0)) ψ γ)

/-- The endomorphism `id + ε • ψ` of the trivial dual-number deformation. -/
def idAddEps (ψ : Module.End k V) :
    Module.End (ArtinianLocalAlgCat.dualNumber Λ k).carrier (trivialModule Λ k V) :=
  let epsilon : (ArtinianLocalAlgCat.dualNumber Λ k).carrier := DualNumber.eps
  LinearMap.id + epsilon • extendEnd Λ k V ψ

/-- `idAddEps ψ` is the `k[ε]`-linear map `id + ε • extendEnd ψ`. -/
theorem idAddEps_def (ψ : Module.End k V) :
    idAddEps Λ k ψ =
      (let epsilon : (ArtinianLocalAlgCat.dualNumber Λ k).carrier := DualNumber.eps
       LinearMap.id + epsilon • extendEnd Λ k V ψ) := rfl

/-- The automorphism of the trivial dual-number object induced by `id + ε ψ` for
an invariant endomorphism `ψ`. -/
def idAddEpsIso (ρ0 : Γ →* LinearMap.GeneralLinearGroup k V)
    (ψ : (endRepresentation Γ Λ k ρ0).invariants) :
    trivialDeformationObj Γ Λ k ρ0 ≅ trivialDeformationObj Γ Λ k ρ0 := by
  let X := trivialDeformationObj Γ Λ k ρ0
  have laws :
      (∀ φ : (endRepresentation Γ Λ k ρ0).invariants,
        (∀ γ m, idAddEps Λ k φ.val ((X.rho γ).val m) =
          (X.rho γ).val (idAddEps Λ k φ.val m)) ∧
        (∀ ha hs, IsIso (GroupRepCat.induced (X := X) (Y := X)
          (𝟙 X.base) (fun m ↦ idAddEps Λ k φ.val m) ha hs))) ∧
      (∀ φ : (endRepresentation Γ Λ k ρ0).invariants,
        (idAddEps Λ k (-φ.val)).comp (idAddEps Λ k φ.val) = LinearMap.id) := sorry
  let arrow (φ : (endRepresentation Γ Λ k ρ0).invariants) : X ⟶ X :=
    Hom.of (𝟙 X.base) (fun m ↦ idAddEps Λ k φ.val m)
      (idAddEps Λ k φ.val).map_add (fun a m ↦ (idAddEps Λ k φ.val).map_smul a m)
      (laws.1 φ).1 ((laws.1 φ).2 _ _)
  exact
    { hom := arrow ψ
      inv := arrow (-ψ)
      hom_inv_id := Hom.ext (Category.id_comp _) (funext (fun m ↦
        LinearMap.congr_fun (laws.2 ψ) m))
      inv_hom_id := Hom.ext (Category.id_comp _) (funext (fun m ↦ by
        change idAddEps Λ k ψ.val (idAddEps Λ k (-ψ.val) m) = m
        simpa only [Submodule.coe_neg, neg_neg, LinearMap.comp_apply, LinearMap.id_apply] using
          LinearMap.congr_fun (laws.2 (-ψ)) m)) }

/-- The underlying forward map of `idAddEpsIso` is `idAddEps`. -/
theorem idAddEpsIso_hom (ρ0 : Γ →* LinearMap.GeneralLinearGroup k V)
    (ψ : (endRepresentation Γ Λ k ρ0).invariants) :
    (idAddEpsIso Γ Λ k ρ0 ψ).hom.toFun = fun m ↦ idAddEps Λ k ψ.val m := rfl

/-- The map `H^0(Γ, End_k(V)) → Inf_{x0}(F)` sending `ψ` to the infinitesimal automorphism
`id + ε ψ`. -/
def infAutOfInvariants (ρ0 : Γ →* LinearMap.GeneralLinearGroup k V)
    (ψ : (endRepresentation Γ Λ k ρ0).invariants) :
    Functor.infinitesimalAutomorphismsAt (forget Γ Λ k) (residueObj Γ Λ k ρ0)
      (trivialDeformation Γ Λ k ρ0) (trivialPushforward Γ Λ k ρ0) :=
  by
    have vertical : (forget Γ Λ k).IsHomLift (𝟙 (ArtinianLocalAlgCat.dualNumber Λ k))
        (idAddEpsIso Γ Λ k ρ0 ψ).hom :=
      IsHomLift.of_fac (forget Γ Λ k) _ _ rfl rfl (by
        change 𝟙 (ArtinianLocalAlgCat.dualNumber Λ k) = 𝟙 _ ≫ 𝟙 _ ≫ 𝟙 _
        exact (Category.id_comp _).symm.trans (congrArg (fun z ↦ 𝟙 _ ≫ z)
          (Category.id_comp _).symm))
    have law : Fiber.isoMk (idAddEpsIso Γ Λ k ρ0 ψ) vertical ∈
        infinitesimalAutomorphismsAt (forget Γ Λ k) (residueObj Γ Λ k ρ0)
          (trivialDeformation Γ Λ k ρ0) (trivialPushforward Γ Λ k ρ0) := sorry
    exact ⟨Fiber.isoMk (idAddEpsIso Γ Λ k ρ0 ψ) vertical, law⟩

/-- Elements of the image of `infAutOfInvariants` are represented by `id + ε ψ`. -/
theorem infAutOfInvariants_spec (ρ0 : Γ →* LinearMap.GeneralLinearGroup k V)
    (ψ : (endRepresentation Γ Λ k ρ0).invariants) :
    (Fiber.fiberInclusion.map (infAutOfInvariants Γ Λ k ρ0 ψ).val.hom).toFun =
      fun m ↦ idAddEps Λ k ψ.val m := rfl

/-- The identification `H^0(Γ, End_k(V)) → Inf_{x0}(F)` sends addition to composition of
automorphisms. -/
theorem infAutOfInvariants_map_add (ρ0 : Γ →* LinearMap.GeneralLinearGroup k V)
    (ψ φ : (endRepresentation Γ Λ k ρ0).invariants) :
    infAutOfInvariants Γ Λ k ρ0 (ψ + φ) =
      infAutOfInvariants Γ Λ k ρ0 ψ * infAutOfInvariants Γ Λ k ρ0 φ := sorry

/-- Invariant endomorphisms biject with infinitesimal automorphisms via `ψ ↦ id + εψ`. -/
theorem infAutOfInvariants_bijective (ρ0 : Γ →* LinearMap.GeneralLinearGroup k V) :
    Function.Bijective (infAutOfInvariants Γ Λ k ρ0) := sorry

/-- Infinitesimal automorphisms of the trivial dual-number representation, viewed additively. -/
abbrev infinitesimalSpace (ρ0 : Γ →* LinearMap.GeneralLinearGroup k V) :=
  Additive (infinitesimalAutomorphismsAt (forget Γ Λ k) (residueObj Γ Λ k ρ0)
    (trivialDeformation Γ Λ k ρ0) (trivialPushforward Γ Λ k ρ0))

/-- Invariant endomorphisms map additively to infinitesimal automorphisms by `ψ ↦ id + εψ`. -/
def invariantsToInfinitesimal (ρ0 : Γ →* LinearMap.GeneralLinearGroup k V) :
    (endRepresentation Γ Λ k ρ0).invariants →+ infinitesimalSpace Γ Λ k ρ0 :=
  AddMonoidHom.mk' (fun ψ ↦ Additive.ofMul (infAutOfInvariants Γ Λ k ρ0 ψ))
    (infAutOfInvariants_map_add Γ Λ k ρ0)

/-- Invariant endomorphisms and infinitesimal automorphisms are additively equivalent
through `ψ ↦ id + εψ`. -/
def invariantsInfinitesimalAddEquiv (ρ0 : Γ →* LinearMap.GeneralLinearGroup k V) :
    (endRepresentation Γ Λ k ρ0).invariants ≃+ infinitesimalSpace Γ Λ k ρ0 :=
  AddEquiv.ofBijective (invariantsToInfinitesimal Γ Λ k ρ0)
    (infAutOfInvariants_bijective Γ Λ k ρ0)

/-- Infinitesimal representation automorphisms commute under composition. -/
instance instAddCommGroupInfinitesimalSpace (ρ0 : Γ →* LinearMap.GeneralLinearGroup k V) :
    AddCommGroup (infinitesimalSpace Γ Λ k ρ0) :=
  { (inferInstance : AddGroup (infinitesimalSpace Γ Λ k ρ0)) with
    add_comm := fun a b ↦ by
      apply (invariantsInfinitesimalAddEquiv Γ Λ k ρ0).symm.injective
      rw [_root_.map_add, _root_.map_add, add_comm] }

/-- Scalar multiplication on infinitesimal automorphisms is induced by their invariant
endomorphism coordinates and preserves composition-defined addition. -/
instance instModuleInfinitesimalSpace (ρ0 : Γ →* LinearMap.GeneralLinearGroup k V) :
    Module k (infinitesimalSpace Γ Λ k ρ0) :=
  (invariantsInfinitesimalAddEquiv Γ Λ k ρ0).symm.module k

/-- Invariant-endomorphism coordinates give a linear equivalence with infinitesimal
representation automorphisms. -/
def invariantsEquivInfinitesimal (ρ0 : Γ →* LinearMap.GeneralLinearGroup k V) :
    (endRepresentation Γ Λ k ρ0).invariants ≃ₗ[k] infinitesimalSpace Γ Λ k ρ0 :=
  ((invariantsInfinitesimalAddEquiv Γ Λ k ρ0).symm.linearEquiv k).symm

/-- Degree-zero group cohomology of endomorphisms is linearly equivalent to the
infinitesimal representation automorphism space. -/
def h0EquivInfinitesimal (ρ0 : Γ →* LinearMap.GeneralLinearGroup k V) :
    groupCohomology.H0 (Rep.of (endRepresentation Γ Λ k ρ0)) ≃ₗ[k]
      infinitesimalSpace Γ Λ k ρ0 :=
  (groupCohomology.H0Iso (Rep.of (endRepresentation Γ Λ k ρ0))).toLinearEquiv.trans
    (invariantsEquivInfinitesimal Γ Λ k ρ0)

/-- The degree-zero comparison sends invariant coordinates to the automorphism `id + εψ`. -/
theorem h0EquivInfinitesimal_apply (ρ0 : Γ →* LinearMap.GeneralLinearGroup k V)
    (x : groupCohomology.H0 (Rep.of (endRepresentation Γ Λ k ρ0))) :
    h0EquivInfinitesimal Γ Λ k ρ0 x =
      Additive.ofMul (infAutOfInvariants Γ Λ k ρ0
        ((groupCohomology.H0Iso (Rep.of (endRepresentation Γ Λ k ρ0))).hom x)) := rfl

/-- Infinitesimal automorphisms of a finite-dimensional representation form a
finite-dimensional vector space. -/
instance instFiniteDimensionalInfinitesimalSpace (ρ0 : Γ →* LinearMap.GeneralLinearGroup k V) :
    FiniteDimensional k (infinitesimalSpace Γ Λ k ρ0) :=
  (invariantsEquivInfinitesimal Γ Λ k ρ0).finiteDimensional

/-- The tangent space `T Def_{V, ρ0}` as isomorphism classes of dual-number fibre objects of
`deformationForget ρ0`. -/
def tangentSpace (ρ0 : Γ →* LinearMap.GeneralLinearGroup k V) : Type (u + 1) :=
  isomorphismClasses.obj (Cat.of ((deformationForget Γ Λ k ρ0).Fiber
    (ArtinianLocalAlgCat.dualNumber Λ k)))

/-- The tangent quotient carries the canonical addition of the residue slice. -/
instance instAddCommGroupTangentSpace (ρ0 : Γ →* LinearMap.GeneralLinearGroup k V) :
    AddCommGroup (tangentSpace Γ Λ k ρ0) :=
  instAddCommGroup_fiberDualTangent (sliceAt (forget Γ Λ k) (residueObj Γ Λ k ρ0))

/-- The tangent quotient carries canonical scalar multiplication by scaling epsilon. -/
instance instModuleTangentSpace (ρ0 : Γ →* LinearMap.GeneralLinearGroup k V) :
    Module k (tangentSpace Γ Λ k ρ0) :=
  instModule_tangentSpaceAt (forget Γ Λ k) (residueObj Γ Λ k ρ0)

/-- Unfolding of `tangentSpace`. -/
theorem tangentSpace_def (ρ0 : Γ →* LinearMap.GeneralLinearGroup k V) :
    tangentSpace Γ Λ k ρ0 =
      isomorphismClasses.obj (Cat.of ((deformationForget Γ Λ k ρ0).Fiber
        (ArtinianLocalAlgCat.dualNumber Λ k))) := rfl

/-- The isomorphism class of a dual-number lift of `(V, ρ0)`. -/
def tangentSpace.mk (ρ0 : Γ →* LinearMap.GeneralLinearGroup k V)
    (x : (deformationForget Γ Λ k ρ0).Fiber (ArtinianLocalAlgCat.dualNumber Λ k)) :
    tangentSpace Γ Λ k ρ0 :=
  Quotient.mk'' x

/-- `tangentSpace.mk` is the class of the given dual-number fibre object. -/
theorem tangentSpace.mk_eq (ρ0 : Γ →* LinearMap.GeneralLinearGroup k V)
    (x : (deformationForget Γ Λ k ρ0).Fiber (ArtinianLocalAlgCat.dualNumber Λ k)) :
    tangentSpace.mk Γ Λ k ρ0 x = Quotient.mk'' x := rfl

/-- The dual-number module on the middle representation of a zero-composite self-sequence
has scalar action `(a + bε)m = am + b f(g(m))`. -/
@[reducible]
def ofExtensionModule (ρ0 : Γ →* LinearMap.GeneralLinearGroup k V)
    (E : Rep.{u} k Γ) (f : Rep.of (residueRepresentation Γ Λ k ρ0) ⟶ E)
    (g : E ⟶ Rep.of (residueRepresentation Γ Λ k ρ0)) (w : f ≫ g = 0) :
    Module (ArtinianLocalAlgCat.dualNumber Λ k).carrier E.V := by
  let act (x : (ArtinianLocalAlgCat.dualNumber Λ k).carrier) (m : E.V) :=
    x.fst • m + x.snd • f.hom (g.hom m)
  have laws :
      (∀ m, act 1 m = m) ∧
      (∀ x y m, act (x * y) m = act x (act y m)) ∧
      (∀ x, act x 0 = 0) ∧
      (∀ x m n, act x (m + n) = act x m + act x n) ∧
      (∀ x y m, act (x + y) m = act x m + act y m) ∧
      (∀ m, act 0 m = 0) := sorry
  exact
    { smul := act
      one_smul := laws.1
      mul_smul := laws.2.1
      smul_zero := laws.2.2.1
      smul_add := laws.2.2.2.1
      add_smul := laws.2.2.2.2.1
      zero_smul := laws.2.2.2.2.2 }

/-- A short exact self-extension becomes a finite projective dual-number representation,
with epsilon acting by inclusion after projection. -/
def ofExtensionObj (ρ0 : Γ →* LinearMap.GeneralLinearGroup k V)
    (E : Rep.{u} k Γ) (f : Rep.of (residueRepresentation Γ Λ k ρ0) ⟶ E)
    (g : E ⟶ Rep.of (residueRepresentation Γ Λ k ρ0)) (w : f ≫ g = 0)
    (h : (ShortComplex.mk f g w).ShortExact) : GroupRepCat Γ Λ k := by
  let D := (ArtinianLocalAlgCat.dualNumber Λ k).carrier
  let μ := ofExtensionModule Γ Λ k ρ0 E f g w
  let M : ModuleCat D := @ModuleCat.of D _ E.V _ μ
  have laws :
      Module.FiniteProjective D M ∧
      (∀ γ (a : D) (m : M), E.ρ γ (a • m) = a • E.ρ γ m) ∧
      (∀ γ m, E.ρ γ (E.ρ γ⁻¹ m) = m) ∧
      (∀ γ m, E.ρ γ⁻¹ (E.ρ γ m) = m) ∧
      (∀ m, E.ρ 1 m = m) ∧
      (∀ γ δ m, E.ρ (γ * δ) m = E.ρ γ (E.ρ δ m)) := sorry
  let action (γ : Γ) : Module.End D M :=
    { toFun := fun m ↦ E.ρ γ m
      map_add' := (E.ρ γ).map_add
      map_smul' := laws.2.1 γ }
  let units (γ : Γ) : LinearMap.GeneralLinearGroup D M :=
    ⟨action γ, action γ⁻¹,
      LinearMap.ext (laws.2.2.1 γ), LinearMap.ext (laws.2.2.2.1 γ)⟩
  exact GroupRepCat.of (ArtinianLocalAlgCat.dualNumber Λ k) E.V
    (isModule := μ) laws.1
    { toFun := units
      map_one' := Units.ext (LinearMap.ext laws.2.2.2.2.1)
      map_mul' γ δ := Units.ext (LinearMap.ext (laws.2.2.2.2.2 γ δ)) }

/-- The scalar action stored in the extension-induced deformation is the prescribed
sum of the residue action and the inclusion–projection term. -/
theorem ofExtensionObj_smul (ρ0 : Γ →* LinearMap.GeneralLinearGroup k V)
    (E : Rep.{u} k Γ) (f : Rep.of (residueRepresentation Γ Λ k ρ0) ⟶ E)
    (g : E ⟶ Rep.of (residueRepresentation Γ Λ k ρ0)) (w : f ≫ g = 0)
    (h : (ShortComplex.mk f g w).ShortExact)
    (x : (ArtinianLocalAlgCat.dualNumber Λ k).carrier) (m : E.V) :
    (ofExtensionObj Γ Λ k ρ0 E f g w h).isModule.smul x m =
      x.fst • m + x.snd • f.hom (g.hom m) := rfl

/-- The extension-induced deformation lies over the dual numbers. -/
theorem ofExtensionObj_base (ρ0 : Γ →* LinearMap.GeneralLinearGroup k V)
    (E : Rep.{u} k Γ) (f : Rep.of (residueRepresentation Γ Λ k ρ0) ⟶ E)
    (g : E ⟶ Rep.of (residueRepresentation Γ Λ k ρ0)) (w : f ≫ g = 0)
    (h : (ShortComplex.mk f g w).ShortExact) :
    (ofExtensionObj Γ Λ k ρ0 E f g w h).base = ArtinianLocalAlgCat.dualNumber Λ k := rfl

/-- The projection of a short exact self-extension is the reduction morphism of its
associated dual-number representation. -/
def ofExtensionHom (ρ0 : Γ →* LinearMap.GeneralLinearGroup k V)
    (E : Rep.{u} k Γ) (f : Rep.of (residueRepresentation Γ Λ k ρ0) ⟶ E)
    (g : E ⟶ Rep.of (residueRepresentation Γ Λ k ρ0)) (w : f ≫ g = 0)
    (h : (ShortComplex.mk f g w).ShortExact) :
    ofExtensionObj Γ Λ k ρ0 E f g w h ⟶ ofResidue Γ Λ k ρ0 := by
  let X := ofExtensionObj Γ Λ k ρ0 E f g w h
  let Y := ofResidue Γ Λ k ρ0
  let base := ArtinianLocalAlgCat.dualNumberToResidue Λ k
  let t : X.module → Y.module := fun m ↦ g.hom m
  have laws :
      (∀ (a : X.base.carrier) m, t (a • m) =
        Y.isModule.smul (ArtinianLocalAlgCat.Hom.toRingHom base a) (t m)) ∧
      (∀ γ m, t ((X.rho γ).val m) = (Y.rho γ).val (t m)) ∧
      (∀ ha hs, IsIso (GroupRepCat.induced (X := X) (Y := Y) base t ha hs)) := sorry
  exact Hom.of base t g.hom.map_add laws.1 laws.2.1 (laws.2.2 _ _)

/-- The underlying reduction function is the original extension projection. -/
theorem ofExtensionHom_toFun (ρ0 : Γ →* LinearMap.GeneralLinearGroup k V)
    (E : Rep.{u} k Γ) (f : Rep.of (residueRepresentation Γ Λ k ρ0) ⟶ E)
    (g : E ⟶ Rep.of (residueRepresentation Γ Λ k ρ0)) (w : f ≫ g = 0)
    (h : (ShortComplex.mk f g w).ShortExact) :
    (ofExtensionHom Γ Λ k ρ0 E f g w h).toFun = fun m ↦ g.hom m := rfl

/-- A short exact self-extension determines a residue-framed deformation over the dual numbers. -/
def ofExtensionFiber (ρ0 : Γ →* LinearMap.GeneralLinearGroup k V)
    (E : Rep.{u} k Γ) (f : Rep.of (residueRepresentation Γ Λ k ρ0) ⟶ E)
    (g : E ⟶ Rep.of (residueRepresentation Γ Λ k ρ0)) (w : f ≫ g = 0)
    (h : (ShortComplex.mk f g w).ShortExact) :
    (deformationForget Γ Λ k ρ0).Fiber (ArtinianLocalAlgCat.dualNumber Λ k) :=
  ⟨Over.mk (ofExtensionHom Γ Λ k ρ0 E f g w h), rfl⟩

/-- The fiber inclusion retains the extension's reduction morphism. -/
theorem ofExtensionFiber_obj (ρ0 : Γ →* LinearMap.GeneralLinearGroup k V)
    (E : Rep.{u} k Γ) (f : Rep.of (residueRepresentation Γ Λ k ρ0) ⟶ E)
    (g : E ⟶ Rep.of (residueRepresentation Γ Λ k ρ0)) (w : f ≫ g = 0)
    (h : (ShortComplex.mk f g w).ShortExact) :
    Fiber.fiberInclusion.obj (ofExtensionFiber Γ Λ k ρ0 E f g w h) =
      Over.mk (ofExtensionHom Γ Λ k ρ0 E f g w h) := rfl

/-- A short exact self-extension defines the tangent class of its dual-number deformation. -/
def ofExtension (ρ0 : Γ →* LinearMap.GeneralLinearGroup k V)
    (E : Rep.{u} k Γ) (f : Rep.of (residueRepresentation Γ Λ k ρ0) ⟶ E)
    (g : E ⟶ Rep.of (residueRepresentation Γ Λ k ρ0)) (w : f ≫ g = 0)
    (h : (ShortComplex.mk f g w).ShortExact) : tangentSpace Γ Λ k ρ0 :=
  tangentSpace.mk Γ Λ k ρ0 (ofExtensionFiber Γ Λ k ρ0 E f g w h)

/-- The extension-to-tangent map is the class of the extension-induced deformation. -/
theorem ofExtension_spec (ρ0 : Γ →* LinearMap.GeneralLinearGroup k V)
    (E : Rep.{u} k Γ) (f : Rep.of (residueRepresentation Γ Λ k ρ0) ⟶ E)
    (g : E ⟶ Rep.of (residueRepresentation Γ Λ k ρ0)) (w : f ≫ g = 0)
    (h : (ShortComplex.mk f g w).ShortExact) :
    ofExtension Γ Λ k ρ0 E f g w h =
      tangentSpace.mk Γ Λ k ρ0 (ofExtensionFiber Γ Λ k ρ0 E f g w h) := rfl

/-- Two self-extensions yield equal tangent classes exactly when their middle representations
are isomorphic by a map commuting with both endpoint maps. -/
theorem ofExtension_iso_iff (ρ0 : Γ →* LinearMap.GeneralLinearGroup k V)
    (E : Rep.{u} k Γ) (f : Rep.of (residueRepresentation Γ Λ k ρ0) ⟶ E)
    (g : E ⟶ Rep.of (residueRepresentation Γ Λ k ρ0)) (w : f ≫ g = 0)
    (h : (ShortComplex.mk f g w).ShortExact)
    (E' : Rep.{u} k Γ) (f' : Rep.of (residueRepresentation Γ Λ k ρ0) ⟶ E')
    (g' : E' ⟶ Rep.of (residueRepresentation Γ Λ k ρ0)) (w' : f' ≫ g' = 0)
    (h' : (ShortComplex.mk f' g' w').ShortExact) :
    ofExtension Γ Λ k ρ0 E f g w h = ofExtension Γ Λ k ρ0 E' f' g' w' h' ↔
      ∃ e : E ≅ E', f ≫ e.hom = f' ∧ e.hom ≫ g' = g := sorry

/-- Every dual-number tangent class arises from a short exact self-extension. -/
theorem ofExtension_surjective (ρ0 : Γ →* LinearMap.GeneralLinearGroup k V) :
    ∀ t : tangentSpace Γ Λ k ρ0,
      ∃ (E : Rep.{u} k Γ) (f : Rep.of (residueRepresentation Γ Λ k ρ0) ⟶ E)
        (g : E ⟶ Rep.of (residueRepresentation Γ Λ k ρ0)) (w : f ≫ g = 0)
        (h : (ShortComplex.mk f g w).ShortExact),
        ofExtension Γ Λ k ρ0 E f g w h = t := sorry

/-- Tangent classes are linearly equivalent to derived self-extensions, sending each short exact
self-extension's concrete deformation to its canonical Ext class. -/
theorem exists_tangentSpace_ext_equiv (ρ0 : Γ →* LinearMap.GeneralLinearGroup k V) :
    ∃ e : tangentSpace Γ Λ k ρ0 ≃ₗ[k] Abelian.Ext.{u + 1}
        (Rep.of (residueRepresentation Γ Λ k ρ0)) (Rep.of (residueRepresentation Γ Λ k ρ0)) 1,
      ∀ (E : Rep.{u} k Γ) (f : Rep.of (residueRepresentation Γ Λ k ρ0) ⟶ E)
        (g : E ⟶ Rep.of (residueRepresentation Γ Λ k ρ0)) (w : f ≫ g = 0)
        (h : (ShortComplex.mk f g w).ShortExact),
        e (ofExtension Γ Λ k ρ0 E f g w h) = h.extClass := sorry

/-- The tangent space of a finite-dimensional representation of a finitely generated
group is finite-dimensional. -/
instance instFiniteDimensionalTangentSpace [Group.FG Γ]
    (ρ0 : Γ →* LinearMap.GeneralLinearGroup k V) :
    FiniteDimensional k (tangentSpace Γ Λ k ρ0) := by
  obtain ⟨e, _⟩ := exists_tangentSpace_ext_equiv Γ Λ k ρ0
  obtain ⟨f⟩ := groupCohomology.nonempty_extIsoH1
    (Rep.of (residueRepresentation Γ Λ k ρ0)) (Rep.of (residueRepresentation Γ Λ k ρ0))
  exact (e.trans f).symm.finiteDimensional

end GroupRepCat
