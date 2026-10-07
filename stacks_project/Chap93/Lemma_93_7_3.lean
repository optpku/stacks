module

public import Mathlib.Algebra.Algebra.Prod
public import Mathlib.Algebra.DualNumber
public import Mathlib.CategoryTheory.Endomorphism
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.RingTheory.Derivation.Basic
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.GradedAlgebra.RingHom
public import Mathlib.RingTheory.LocalRing.Pullback
public import stacks_project.Chap90.Definition_90_12_1_TangentSpace
public import stacks_project.Chap90.Definition_90_16_8_RimSchlessinger
public import stacks_project.Chap90.Remarks_90_5_2_IsoClass
public import stacks_project.Chap93.Example_93_7_1_Graded_algebras

/-!
# Infinitesimal automorphisms and the tangent space of graded-algebra deformations

In the deformation category `Def_P` of Example 93.7.1, `Inf(Def_P)` is identified with
homogeneous degree-0 `k`-derivations `P → P`, and both that space and `T Def_P` are
finite-dimensional whenever `P` is of finite type over `k`.
-/

@[expose] public section

open CategoryTheory Functor
open ArtinianLocalAlgCat
open TrivSqZeroExt

universe u

section HomogeneousDerivations

variable {k A : Type u} [Field k] [CommRing A] [Algebra k A]

namespace Derivation

/-- A derivation is homogeneous of degree 0 when it preserves every homogeneous piece. -/
def IsHomogeneous (𝒜 : ℕ → Submodule k A) (D : Derivation k A A) : Prop :=
  ∀ d x, x ∈ 𝒜 d → D x ∈ 𝒜 d

end Derivation

namespace GradedAlgebra

/-- Homogeneous degree-0 `k`-derivations of an internally graded algebra, as a `k`-submodule of
all `k`-derivations. This is the space `Der_k(P, P)` of Lemma 93.7.3. -/
def homogeneousDerivations (𝒜 : ℕ → Submodule k A) [GradedAlgebra 𝒜] :
    Submodule k (Derivation k A A) where
  carrier := {D | D.IsHomogeneous 𝒜}
  add_mem' := sorry
  zero_mem' := sorry
  smul_mem' := sorry

/-- Membership in `homogeneousDerivations` is degree-0 homogeneity. -/
theorem mem_homogeneousDerivations (𝒜 : ℕ → Submodule k A) [GradedAlgebra 𝒜]
    {D : Derivation k A A} :
    D ∈ homogeneousDerivations 𝒜 ↔ D.IsHomogeneous 𝒜 := sorry

end GradedAlgebra

end HomogeneousDerivations

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable (Λ)

open GradedAlgebra FiniteProjectiveGradedAlgebraCat

namespace FiniteProjectiveGradedAlgebraCat

/-- The slice projection `Def_P ⟶ C_Λ` whose tangent space is `T Def_P`. -/
abbrev deformationForget (P : FiniteProjectiveGradedAlgebra k) :=
  Over.forget (Fiber.fiberInclusion.obj (residueObj Λ P)) ⋙ forget

/-- `deformationForget Λ P` is the composite of the Over-forgetful functor with `forget`. -/
theorem deformationForget_eq (P : FiniteProjectiveGradedAlgebra k) :
    deformationForget Λ P =
      Over.forget (Fiber.fiberInclusion.obj (residueObj Λ P)) ⋙ forget := sorry

/-- The slice projection of `Def_P` is a predeformation category. -/
instance instIsPredeformationCategory_deformationForget
    (P : FiniteProjectiveGradedAlgebra k) :
    IsPredeformationCategory (deformationForget Λ P) := sorry

/-- Predeformation categories are cofibered in groupoids. -/
instance instIsFiberedInGroupoids_deformationForget_op
    (P : FiniteProjectiveGradedAlgebra k) :
    IsFibered.InGroupoids (deformationForget Λ P).op :=
  IsPredeformationCategory.isCofiberedInGroupoids

/-- The inclusion `k ⟶ k[ε]` in `ArtinianLocalAlgCat`. -/
def residueIncl : residue Λ k ⟶ dualNumber Λ k where
  hom :=
    { toFun := fun a ↦ inl (a : k)
      map_one' := sorry
      map_mul' := sorry
      map_zero' := sorry
      map_add' := sorry
      commutes' := sorry }
  isLocalHom := sorry
  residue_compat := sorry

/-- The coefficient projection `k[ε] ⟶ k` in `ArtinianLocalAlgCat`. -/
def dualNumberProj : dualNumber Λ k ⟶ residue Λ k where
  hom :=
    { toFun := fun x ↦ x.fst
      map_one' := sorry
      map_mul' := sorry
      map_zero' := sorry
      map_add' := sorry
      commutes' := sorry }
  isLocalHom := sorry
  residue_compat := sorry

/-- The canonical `k[ε]`-algebra structure on `P[ε] = DualNumber P.carrier`. -/
def dualNumberRingHom (P : FiniteProjectiveGradedAlgebra k) :
    DualNumber k →+* DualNumber P.carrier where
  toFun x := ⟨algebraMap k P.carrier x.fst, algebraMap k P.carrier x.snd⟩
  map_one' := sorry
  map_mul' := sorry
  map_zero' := sorry
  map_add' := sorry

/-- `P[ε]` is a `k[ε]`-algebra via the coefficientwise algebra map. -/
instance instAlgebra_dualNumber (P : FiniteProjectiveGradedAlgebra k) :
    Algebra (dualNumber Λ k).carrier (DualNumber P.carrier) :=
  (dualNumberRingHom P).toAlgebra

/-- The degree-`d` piece of `P[ε]` is `P_d ⊕ ε P_d`. -/
def trivialDeformationGrading (P : FiniteProjectiveGradedAlgebra k) :
    ℕ → Submodule (dualNumber Λ k).carrier (DualNumber P.carrier) := fun d ↦
  { carrier := {x | x.fst ∈ P.grading d ∧ x.snd ∈ P.grading d}
    add_mem' := sorry
    zero_mem' := sorry
    smul_mem' := sorry }

/-- Inclusion of a homogeneous summand as the scalar part of `P[ε]`. -/
def gradingFstEmbed (P : FiniteProjectiveGradedAlgebra k) (d : ℕ) :
    P.grading d →+ trivialDeformationGrading Λ P d where
  toFun a := ⟨⟨(a : P.carrier), 0⟩, sorry⟩
  map_zero' := sorry
  map_add' := sorry

/-- Inclusion of a homogeneous summand as the `ε`-part of `P[ε]`. -/
def gradingSndEmbed (P : FiniteProjectiveGradedAlgebra k) (d : ℕ) :
    P.grading d →+ trivialDeformationGrading Λ P d where
  toFun a := ⟨⟨0, (a : P.carrier)⟩, sorry⟩
  map_zero' := sorry
  map_add' := sorry

/-- Decomposition of `P[ε]` into homogeneous pieces, induced by the decomposition of `P`. -/
def trivialDecompose (P : FiniteProjectiveGradedAlgebra k) :
    DualNumber P.carrier →+ DirectSum ℕ fun d ↦ trivialDeformationGrading Λ P d where
  toFun x :=
    DirectSum.map (gradingFstEmbed Λ P) (DirectSum.decompose P.grading x.fst) +
      DirectSum.map (gradingSndEmbed Λ P) (DirectSum.decompose P.grading x.snd)
  map_zero' := sorry
  map_add' := sorry

/-- The grading `P_d ⊕ ε P_d` makes `P[ε]` an internally graded `k[ε]`-algebra. -/
instance instGradedAlgebra_trivialDeformationGrading (P : FiniteProjectiveGradedAlgebra k) :
    GradedAlgebra (trivialDeformationGrading Λ P) where
  one_mem := sorry
  mul_mem := sorry
  decompose' := trivialDecompose Λ P
  left_inv := sorry
  right_inv := sorry

/-- Each homogeneous piece of `P[ε]` is finite projective over `k[ε]`. -/
instance instIsFiniteProjective_trivialDeformationGrading
    (P : FiniteProjectiveGradedAlgebra k) :
    IsFiniteProjective (trivialDeformationGrading Λ P) := sorry

/-- The trivial dual-number deformation `Q = P ⊗_k k[ε]`, realized as `P[ε]`. -/
def trivialDeformation (P : FiniteProjectiveGradedAlgebra k) :
    FiniteProjectiveGradedAlgebraCat Λ k :=
  of (dualNumber Λ k)
    (FiniteProjectiveGradedAlgebra.of (DualNumber P.carrier) (trivialDeformationGrading Λ P))

/-- The base of the trivial deformation is `k[ε]`. -/
theorem trivialDeformation_base (P : FiniteProjectiveGradedAlgebra k) :
    (trivialDeformation Λ P).base = dualNumber Λ k := sorry

/-- The underlying algebra of the trivial deformation is `DualNumber P.carrier`. -/
theorem trivialDeformation_carrier (P : FiniteProjectiveGradedAlgebra k) :
    (trivialDeformation Λ P).algebra.carrier = DualNumber P.carrier := sorry

/-- The projection `P[ε] → P`, `(a, b) ↦ a`, as a graded ring homomorphism. -/
def trivialDeformationProj (P : FiniteProjectiveGradedAlgebra k) :
    trivialDeformationGrading Λ P →+*ᵍ P.grading where
  toRingHom := (fstHom k P.carrier P.carrier).toRingHom
  map_mem := sorry

/-- The inclusion `P → P[ε]`, `a ↦ (a, 0)`, as a graded ring homomorphism. -/
def trivialDeformationIncl (P : FiniteProjectiveGradedAlgebra k) :
    P.grading →+*ᵍ trivialDeformationGrading Λ P where
  toRingHom := inlHom P.carrier P.carrier
  map_mem := sorry

/-- The morphism `(k[ε], P[ε]) ⟶ (k, P)` over the coefficient projection `k[ε] ⟶ k`. -/
def trivialDeformationToResidue (P : FiniteProjectiveGradedAlgebra k) :
    trivialDeformation Λ P ⟶ ofResidue Λ P :=
  Hom.of (dualNumberProj Λ) (trivialDeformationProj Λ P) sorry sorry

/-- The morphism `(k, P) ⟶ (k[ε], P[ε])` over the inclusion `k ⟶ k[ε]`. -/
def residueToTrivialDeformation (P : FiniteProjectiveGradedAlgebra k) :
    ofResidue Λ P ⟶ trivialDeformation Λ P :=
  Hom.of (residueIncl Λ) (trivialDeformationIncl Λ P) sorry sorry

/-- The trivial deformation as an object of the residue-fibre slice `Def_P`. -/
def trivialDeformationOver (P : FiniteProjectiveGradedAlgebra k) :
    Over (Fiber.fiberInclusion.obj (residueObj Λ P)) :=
  Over.mk (trivialDeformationToResidue Λ P)

/-- The identity object of `Def_P`, lying over the residue field. -/
def deformationResidueOver (P : FiniteProjectiveGradedAlgebra k) :
    Over (Fiber.fiberInclusion.obj (residueObj Λ P)) :=
  Over.mk (𝟙 (Fiber.fiberInclusion.obj (residueObj Λ P)))

/-- The trivial deformation in the dual-number fibre of `deformationForget`. -/
def trivialDeformationFiber (P : FiniteProjectiveGradedAlgebra k) :
    (deformationForget Λ P).Fiber (dualNumber Λ k) :=
  Fiber.mk
    (rfl : (deformationForget Λ P).obj (trivialDeformationOver Λ P) = dualNumber Λ k)

/-- The identity object of `Def_P` in the residue fibre of `deformationForget`. -/
def deformationResidueFiber (P : FiniteProjectiveGradedAlgebra k) :
    (deformationForget Λ P).Fiber (residue Λ k) :=
  Fiber.mk
    (rfl : (deformationForget Λ P).obj (deformationResidueOver Λ P) = residue Λ k)

/-- The ring map `id + ε D` on `P[ε]`. -/
def idAddEpsilonRingHom (P : FiniteProjectiveGradedAlgebra k)
    (D : Derivation k P.carrier P.carrier) :
    DualNumber P.carrier →+* DualNumber P.carrier where
  toFun x := ⟨x.fst, x.snd + D x.fst⟩
  map_one' := sorry
  map_mul' := sorry
  map_zero' := sorry
  map_add' := sorry

/-- `id + ε D` as a graded endomorphism of `P[ε]`. The map preserves the grading
`P_d ⊕ ε P_d` precisely when `D` is homogeneous of degree 0. -/
def idAddEpsilonGradedHom (P : FiniteProjectiveGradedAlgebra k)
    (D : homogeneousDerivations P.grading) :
    trivialDeformationGrading Λ P →+*ᵍ trivialDeformationGrading Λ P where
  toRingHom := idAddEpsilonRingHom P D.val
  map_mem := sorry

/-- `id + ε D` as an endomorphism of the trivial deformation in `F`. -/
def idAddEpsilonHom (P : FiniteProjectiveGradedAlgebra k)
    (D : homogeneousDerivations P.grading) :
    trivialDeformation Λ P ⟶ trivialDeformation Λ P :=
  Hom.of (𝟙 (dualNumber Λ k)) (idAddEpsilonGradedHom Λ P D) sorry sorry

/-- `id + ε D` as an automorphism of the trivial deformation in the dual-number fibre of
`Def_P`. This is the comparison map `Der_k(P, P) → Inf(Def_P)`. -/
def idAddEpsilon (P : FiniteProjectiveGradedAlgebra k)
    (D : homogeneousDerivations P.grading) :
    Aut (trivialDeformationFiber Λ P) where
  hom := ⟨Over.homMk (idAddEpsilonHom Λ P D) sorry, sorry⟩
  inv := ⟨Over.homMk (idAddEpsilonHom Λ P (-D)) sorry, sorry⟩
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The underlying algebra map of `idAddEpsilon D` is `(a, b) ↦ (a, b + D a)`. -/
theorem idAddEpsilon_apply (P : FiniteProjectiveGradedAlgebra k)
    (D : homogeneousDerivations P.grading) (x : DualNumber P.carrier) :
    idAddEpsilonRingHom P D.val x = ⟨x.fst, x.snd + D.val x.fst⟩ := sorry

/-- The comparison `γ = id + ε D` is a monoid homomorphism from homogeneous derivations
to fibre automorphisms of `P[ε]`. -/
theorem idAddEpsilon_map_add (P : FiniteProjectiveGradedAlgebra k)
    (D E : homogeneousDerivations P.grading) :
    idAddEpsilon Λ P (D + E) = idAddEpsilon Λ P D * idAddEpsilon Λ P E := sorry

noncomputable section

/-- Dual-number scaling `a + v ε ↦ a + (c v) ε` as a morphism of `C_Λ`. -/
def dualNumberScaleHom (c : k) : dualNumber Λ k ⟶ dualNumber Λ k where
  hom :=
    { toFun := fun x ↦ ⟨x.fst, c * x.snd⟩
      map_one' := sorry
      map_mul' := sorry
      map_zero' := sorry
      map_add' := sorry
      commutes' := sorry }
  isLocalHom := sorry
  residue_compat := sorry

/-- Dual-number scaling evaluates to `(x.fst, c * x.snd)`. -/
theorem dualNumberScaleHom_apply (c : k) (x : (dualNumber Λ k).carrier) :
    (dualNumberScaleHom Λ c).hom x = ⟨x.fst, c * x.snd⟩ := sorry

/-- The coefficient projection `k[ε] ⟶ k` as a `Λ`-algebra map. -/
def dualNumberCospan : (dualNumber Λ k).carrier →ₐ[Λ] (residue Λ k).carrier :=
  (dualNumberProj Λ).hom

/-- `dualNumberCospan` is the underlying algebra map of `dualNumberProj`. -/
theorem dualNumberCospan_eq :
    dualNumberCospan Λ =
      ((dualNumberProj Λ : dualNumber Λ k ⟶ residue Λ k).hom) := sorry

/-- The coefficient projection is a local homomorphism. -/
instance instIsLocalHom_dualNumberCospan :
    IsLocalHom
      (dualNumberCospan Λ : (dualNumber Λ k).carrier →ₐ[Λ] (residue Λ k).carrier) := sorry

/-- The fibre product `k[ε] ×_k k[ε]` is a local ring. -/
instance instIsLocalRing_dualNumberSelfPullback :
    IsLocalRing
      (AlgHom.pullback
        (dualNumberCospan Λ : (dualNumber Λ k).carrier →ₐ[Λ] (residue Λ k).carrier)
        (dualNumberCospan Λ)) :=
  AlgHom.isLocalRing_pullback
    (dualNumberCospan Λ : (dualNumber Λ k).carrier →ₐ[Λ] (residue Λ k).carrier)
    (dualNumberCospan Λ)

/-- The fibre product `k[ε] ×_k k[ε]` is Artinian. -/
instance instIsArtinianRing_dualNumberSelfPullback :
    IsArtinianRing
      (AlgHom.pullback
        (dualNumberCospan Λ : (dualNumber Λ k).carrier →ₐ[Λ] (residue Λ k).carrier)
        (dualNumberCospan Λ)) := sorry

/-- The canonical section of the first projection `k[ε] → k[ε] ×_k k[ε]`,
sending `a + b ε` to `(a + b ε, a)`. -/
def dualNumberSelfPullbackSectionHom :
    (dualNumber Λ k).carrier →ₐ[Λ]
      AlgHom.pullback
        (dualNumberCospan Λ : (dualNumber Λ k).carrier →ₐ[Λ] (residue Λ k).carrier)
        (dualNumberCospan Λ) :=
  AlgHom.codRestrict
    (AlgHom.prod (AlgHom.id Λ (dualNumber Λ k).carrier)
      (((inlAlgHom k k k).restrictScalars Λ).comp (dualNumberCospan Λ)))
    (AlgHom.pullback
      (dualNumberCospan Λ : (dualNumber Λ k).carrier →ₐ[Λ] (residue Λ k).carrier)
      (dualNumberCospan Λ)) sorry

/-- The first projection of `k[ε] ×_k k[ε]` is a local homomorphism. -/
instance instIsLocalHom_dualNumberSelfPullbackFst :
    IsLocalHom
      (AlgHom.pullbackFst
        (dualNumberCospan Λ : (dualNumber Λ k).carrier →ₐ[Λ] (residue Λ k).carrier)
        (dualNumberCospan Λ)) := sorry

/-- The canonical section of `k[ε] ×_k k[ε]` is a local homomorphism. -/
instance instIsLocalHom_dualNumberSelfPullbackSectionHom :
    IsLocalHom
      (dualNumberSelfPullbackSectionHom Λ :
        (dualNumber Λ k).carrier →ₐ[Λ]
          AlgHom.pullback
            (dualNumberCospan Λ : (dualNumber Λ k).carrier →ₐ[Λ] (residue Λ k).carrier)
            (dualNumberCospan Λ)) := sorry

/-- Residue-field identification of `k[ε] ×_k k[ε]` with `k`. -/
def dualNumberSelfPullbackResidueFieldIso :
    IsLocalRing.ResidueField
      (AlgHom.pullback
        (dualNumberCospan Λ : (dualNumber Λ k).carrier →ₐ[Λ] (residue Λ k).carrier)
        (dualNumberCospan Λ)) ≃ₐ[Λ] k :=
  AlgEquiv.ofAlgHom
    ((dualNumber Λ k).residueFieldIso.toAlgHom.comp
      (IsLocalRing.ResidueField.mapAlgHom
        (AlgHom.pullbackFst
          (dualNumberCospan Λ : (dualNumber Λ k).carrier →ₐ[Λ] (residue Λ k).carrier)
          (dualNumberCospan Λ))))
    ((IsLocalRing.ResidueField.mapAlgHom (dualNumberSelfPullbackSectionHom Λ)).comp
      (dualNumber Λ k).residueFieldIso.symm.toAlgHom)
    sorry sorry

/-- The fibre product `k[ε] ×_k k[ε]` as an object of `C_Λ`. -/
def dualNumberSelfPullback : ArtinianLocalAlgCat Λ k :=
  ArtinianLocalAlgCat.of
    (AlgHom.pullback
      (dualNumberCospan Λ : (dualNumber Λ k).carrier →ₐ[Λ] (residue Λ k).carrier)
      (dualNumberCospan Λ))
    (dualNumberSelfPullbackResidueFieldIso Λ)

/-- The bundled self-pullback has the algebra-pullback carrier. -/
theorem dualNumberSelfPullback_carrier :
    (dualNumberSelfPullback Λ : ArtinianLocalAlgCat Λ k).carrier =
      AlgHom.pullback
        (dualNumberCospan Λ : (dualNumber Λ k).carrier →ₐ[Λ] (residue Λ k).carrier)
        (dualNumberCospan Λ) := sorry

/-- Dual-number addition on the algebra pullback `k[ε] ×_k k[ε]`. -/
def dualNumberAddAlgHom :
    AlgHom.pullback
        (dualNumberCospan Λ : (dualNumber Λ k).carrier →ₐ[Λ] (residue Λ k).carrier)
        (dualNumberCospan Λ) →ₐ[Λ]
      (dualNumber Λ k).carrier where
  toFun p :=
    let a :=
      AlgHom.pullbackFst
        (dualNumberCospan Λ : (dualNumber Λ k).carrier →ₐ[Λ] (residue Λ k).carrier)
        (dualNumberCospan Λ) p
    let b :=
      AlgHom.pullbackSnd
        (dualNumberCospan Λ : (dualNumber Λ k).carrier →ₐ[Λ] (residue Λ k).carrier)
        (dualNumberCospan Λ) p
    ⟨a.fst, a.snd + b.snd⟩
  map_one' := sorry
  map_mul' := sorry
  map_zero' := sorry
  map_add' := sorry
  commutes' := sorry

/-- Dual-number addition `k[ε] ×_k k[ε] ⟶ k[ε]`. -/
def dualNumberAddHom : dualNumberSelfPullback Λ ⟶ dualNumber Λ k where
  hom := dualNumberAddAlgHom Λ
  isLocalHom := sorry
  residue_compat := sorry

/-- Dual-number addition on a pair `(a + b ε, a + c ε)` is `a + (b + c) ε`. -/
theorem dualNumberAddHom_apply
    (p : AlgHom.pullback
      (dualNumberCospan Λ : (dualNumber Λ k).carrier →ₐ[Λ] (residue Λ k).carrier)
      (dualNumberCospan Λ)) :
    dualNumberAddAlgHom Λ p =
      ⟨(AlgHom.pullbackFst
          (dualNumberCospan Λ : (dualNumber Λ k).carrier →ₐ[Λ] (residue Λ k).carrier)
          (dualNumberCospan Λ) p).fst,
        (AlgHom.pullbackFst
            (dualNumberCospan Λ : (dualNumber Λ k).carrier →ₐ[Λ] (residue Λ k).carrier)
            (dualNumberCospan Λ) p).snd +
          (AlgHom.pullbackSnd
            (dualNumberCospan Λ : (dualNumber Λ k).carrier →ₐ[Λ] (residue Λ k).carrier)
            (dualNumberCospan Λ) p).snd⟩ := sorry

/-- The first projection `k[ε] ×_k k[ε] ⟶ k[ε]` in `C_Λ`. -/
def dualNumberSelfPullbackFst : dualNumberSelfPullback Λ ⟶ dualNumber Λ k where
  hom :=
    AlgHom.pullbackFst
      (dualNumberCospan Λ : (dualNumber Λ k).carrier →ₐ[Λ] (residue Λ k).carrier)
      (dualNumberCospan Λ)
  isLocalHom := sorry
  residue_compat := sorry

/-- The second projection `k[ε] ×_k k[ε] ⟶ k[ε]` in `C_Λ`. -/
def dualNumberSelfPullbackSnd : dualNumberSelfPullback Λ ⟶ dualNumber Λ k where
  hom :=
    AlgHom.pullbackSnd
      (dualNumberCospan Λ : (dualNumber Λ k).carrier →ₐ[Λ] (residue Λ k).carrier)
      (dualNumberCospan Λ)
  isLocalHom := sorry
  residue_compat := sorry

/-- The two projections of `k[ε] ×_k k[ε]` agree after reducing to `k`. -/
theorem dualNumberSelfPullbackFst_comp_proj :
    (dualNumberSelfPullbackFst Λ ≫ dualNumberProj Λ :
        dualNumberSelfPullback Λ ⟶ residue Λ k) =
      dualNumberSelfPullbackSnd Λ ≫ dualNumberProj Λ := sorry

/-- The second projection reduces to the same residue map as the first projection. -/
theorem dualNumberSelfPullbackSnd_comp_proj :
    (dualNumberSelfPullbackSnd Λ ≫ dualNumberProj Λ :
        dualNumberSelfPullback Λ ⟶ residue Λ k) =
      dualNumberSelfPullbackFst Λ ≫ dualNumberProj Λ := sorry

/-- The composite projection `k[ε] ×_k k[ε] ⟶ k` through the first factor. -/
def dualNumberSelfPullbackToResidue : dualNumberSelfPullback Λ ⟶ residue Λ k :=
  dualNumberSelfPullbackFst Λ ≫ dualNumberProj Λ

/-- `dualNumberSelfPullbackToResidue` is the first projection followed by `dualNumberProj`. -/
theorem dualNumberSelfPullbackToResidue_eq :
    dualNumberSelfPullbackToResidue Λ =
      (dualNumberSelfPullbackFst Λ ≫ dualNumberProj Λ :
        dualNumberSelfPullback Λ ⟶ residue Λ k) := sorry

/-- The slice projection of `Def_P` satisfies the Rim–Schlessinger condition. -/
instance instHasRimSchlessinger_deformationForget
    (P : FiniteProjectiveGradedAlgebra k) :
    HasRimSchlessinger (deformationForget Λ P) := sorry

/-- The underlying algebra of a dual-number fibre object, as a `k[ε]`-algebra via the fibre
identification of its base. -/
def fiberAlgebraMap (P : FiniteProjectiveGradedAlgebra k)
    (x : (deformationForget Λ P).Fiber (dualNumber Λ k)) :
    (dualNumber Λ k).carrier →+* x.1.left.algebra.carrier :=
  (algebraMap x.1.left.base.carrier x.1.left.algebra.carrier).comp
    (eqToHom x.property.symm).hom.toRingHom

/-- `fiberAlgebraMap` is the structure map of the fibre algebra after transporting the base
along the fibre equality. -/
theorem fiberAlgebraMap_eq (P : FiniteProjectiveGradedAlgebra k)
    (x : (deformationForget Λ P).Fiber (dualNumber Λ k)) :
    fiberAlgebraMap Λ P x =
      (algebraMap x.1.left.base.carrier x.1.left.algebra.carrier).comp
        (eqToHom x.property.symm).hom.toRingHom := sorry

/-- The reduction of a dual-number fibre object to `P`, as a ring homomorphism. -/
def reductionRingHom (P : FiniteProjectiveGradedAlgebra k)
    (x : (deformationForget Λ P).Fiber (dualNumber Λ k)) :
    x.1.left.algebra.carrier →+* P.carrier :=
  x.1.hom.gradedHom.toRingHom

/-- `reductionRingHom` is the underlying ring map of the graded structure morphism to `P`. -/
theorem reductionRingHom_eq (P : FiniteProjectiveGradedAlgebra k)
    (x : (deformationForget Λ P).Fiber (dualNumber Λ k)) :
    reductionRingHom Λ P x = x.1.hom.gradedHom.toRingHom := sorry

/-- The underlying algebra of the Rim–Schlessinger fibre product of two dual-number
deformations, as the ring pullback of their reductions to `P`. -/
abbrev baerSumPullbackCarrier (P : FiniteProjectiveGradedAlgebra k)
    (x y : (deformationForget Λ P).Fiber (dualNumber Λ k)) : Type u :=
  ↥(RingHom.pullback (reductionRingHom Λ P x) (reductionRingHom Λ P y))

/-- An element of `baerSumPullbackCarrier` is a pair of algebra elements with the same
reduction to `P`. -/
theorem baerSumPullbackCarrier_fst_eq_snd (P : FiniteProjectiveGradedAlgebra k)
    (x y : (deformationForget Λ P).Fiber (dualNumber Λ k))
    (z : baerSumPullbackCarrier Λ P x y) :
    reductionRingHom Λ P x
        (RingHom.pullbackFst (reductionRingHom Λ P x) (reductionRingHom Λ P y) z) =
      reductionRingHom Λ P y
        (RingHom.pullbackSnd (reductionRingHom Λ P x) (reductionRingHom Λ P y) z) := sorry

/-- The `k[ε] ×_k k[ε]`-algebra map on the pullback of two dual-number deformations,
acting componentwise through `fiberAlgebraMap`. -/
def baerSumPullbackRingHom (P : FiniteProjectiveGradedAlgebra k)
    (x y : (deformationForget Λ P).Fiber (dualNumber Λ k)) :
    (dualNumberSelfPullback Λ : ArtinianLocalAlgCat Λ k).carrier →+*
      baerSumPullbackCarrier Λ P x y where
  toFun p :=
    ⟨(fiberAlgebraMap Λ P x
        ((dualNumberSelfPullbackFst Λ : dualNumberSelfPullback Λ ⟶ dualNumber Λ k).hom p),
      fiberAlgebraMap Λ P y
        ((dualNumberSelfPullbackSnd Λ : dualNumberSelfPullback Λ ⟶ dualNumber Λ k).hom p)),
      sorry⟩
  map_one' := sorry
  map_mul' := sorry
  map_zero' := sorry
  map_add' := sorry

/-- `baerSumPullbackRingHom` acts by the two `fiberAlgebraMap`s on the pair of dual-number
coefficients. -/
theorem baerSumPullbackRingHom_apply (P : FiniteProjectiveGradedAlgebra k)
    (x y : (deformationForget Λ P).Fiber (dualNumber Λ k))
    (p : (dualNumberSelfPullback Λ).carrier) :
    (baerSumPullbackRingHom Λ P x y p :
        x.1.left.algebra.carrier × y.1.left.algebra.carrier) =
      (fiberAlgebraMap Λ P x ((dualNumberSelfPullbackFst Λ).hom p),
        fiberAlgebraMap Λ P y ((dualNumberSelfPullbackSnd Λ).hom p)) := sorry

/-- The pullback of two dual-number deformations is a `k[ε] ×_k k[ε]`-algebra. -/
instance instAlgebra_baerSumPullbackCarrier (P : FiniteProjectiveGradedAlgebra k)
    (x y : (deformationForget Λ P).Fiber (dualNumber Λ k)) :
    Algebra (dualNumberSelfPullback Λ : ArtinianLocalAlgCat Λ k).carrier
      (baerSumPullbackCarrier Λ P x y) :=
  (baerSumPullbackRingHom Λ P x y).toAlgebra

/-- The degree-`d` piece of the fibre product is the pullback of the two degree-`d` pieces. -/
def baerSumPullbackGrading (P : FiniteProjectiveGradedAlgebra k)
    (x y : (deformationForget Λ P).Fiber (dualNumber Λ k)) :
    ℕ → Submodule (dualNumberSelfPullback Λ : ArtinianLocalAlgCat Λ k).carrier
      (baerSumPullbackCarrier Λ P x y) :=
  fun d ↦
    { carrier :=
        {z |
          RingHom.pullbackFst (reductionRingHom Λ P x) (reductionRingHom Λ P y) z ∈
              x.1.left.algebra.grading d ∧
            RingHom.pullbackSnd (reductionRingHom Λ P x) (reductionRingHom Λ P y) z ∈
              y.1.left.algebra.grading d}
      add_mem' := sorry
      zero_mem' := sorry
      smul_mem' := sorry }

/-- Membership in a homogeneous piece of the fibre product is membership in both degree-`d`
pieces. -/
theorem mem_baerSumPullbackGrading (P : FiniteProjectiveGradedAlgebra k)
    (x y : (deformationForget Λ P).Fiber (dualNumber Λ k)) {d : ℕ}
    {z : baerSumPullbackCarrier Λ P x y} :
    z ∈ baerSumPullbackGrading Λ P x y d ↔
      RingHom.pullbackFst (reductionRingHom Λ P x) (reductionRingHom Λ P y) z ∈
          x.1.left.algebra.grading d ∧
        RingHom.pullbackSnd (reductionRingHom Λ P x) (reductionRingHom Λ P y) z ∈
          y.1.left.algebra.grading d := sorry

/-- Decomposition of the fibre-product algebra into homogeneous pieces, pairing the
decompositions of the two factors. -/
def baerSumPullbackDecompose (P : FiniteProjectiveGradedAlgebra k)
    (x y : (deformationForget Λ P).Fiber (dualNumber Λ k)) :
    baerSumPullbackCarrier Λ P x y →+
      DirectSum ℕ fun d ↦ baerSumPullbackGrading Λ P x y d where
  toFun z :=
    DFinsupp.zipWith
      (fun (d : ℕ) (q : x.1.left.algebra.grading d) (r : y.1.left.algebra.grading d) ↦
        (⟨⟨((q : x.1.left.algebra.carrier), (r : y.1.left.algebra.carrier)), sorry⟩, sorry⟩ :
          baerSumPullbackGrading Λ P x y d))
      (fun _d ↦ Subtype.ext (Subtype.ext rfl))
      (DirectSum.decompose x.1.left.algebra.grading
        (RingHom.pullbackFst (reductionRingHom Λ P x) (reductionRingHom Λ P y) z))
      (DirectSum.decompose y.1.left.algebra.grading
        (RingHom.pullbackSnd (reductionRingHom Λ P x) (reductionRingHom Λ P y) z))
  map_zero' := sorry
  map_add' := sorry

/-- The degree-`d` component of `baerSumPullbackDecompose` is the pair of degree-`d`
components of the two factors. -/
theorem baerSumPullbackDecompose_apply (P : FiniteProjectiveGradedAlgebra k)
    (x y : (deformationForget Λ P).Fiber (dualNumber Λ k))
    (z : baerSumPullbackCarrier Λ P x y) (d : ℕ) :
    ((baerSumPullbackDecompose Λ P x y z d : baerSumPullbackCarrier Λ P x y) :
        x.1.left.algebra.carrier × y.1.left.algebra.carrier) =
      ((DirectSum.decompose x.1.left.algebra.grading
          (RingHom.pullbackFst (reductionRingHom Λ P x) (reductionRingHom Λ P y) z) d :
          x.1.left.algebra.carrier),
        (DirectSum.decompose y.1.left.algebra.grading
          (RingHom.pullbackSnd (reductionRingHom Λ P x) (reductionRingHom Λ P y) z) d :
          y.1.left.algebra.carrier)) := sorry

/-- The pullback of two internally graded dual-number deformations is internally graded. -/
instance instGradedAlgebra_baerSumPullbackGrading (P : FiniteProjectiveGradedAlgebra k)
    (x y : (deformationForget Λ P).Fiber (dualNumber Λ k)) :
    GradedAlgebra (baerSumPullbackGrading Λ P x y) where
  one_mem := sorry
  mul_mem := sorry
  decompose' := baerSumPullbackDecompose Λ P x y
  left_inv := sorry
  right_inv := sorry

/-- Each homogeneous piece of the fibre product is finite projective over `k[ε] ×_k k[ε]`. -/
instance instIsFiniteProjective_baerSumPullbackGrading
    (P : FiniteProjectiveGradedAlgebra k)
    (x y : (deformationForget Λ P).Fiber (dualNumber Λ k)) :
    IsFiniteProjective (baerSumPullbackGrading Λ P x y) := sorry

/-- The pair `(k[ε] ×_k k[ε], Q ×_P R)` as an object of `F`. -/
def baerSumPullbackObj (P : FiniteProjectiveGradedAlgebra k)
    (x y : (deformationForget Λ P).Fiber (dualNumber Λ k)) :
    FiniteProjectiveGradedAlgebraCat Λ k :=
  of (dualNumberSelfPullback Λ)
    (FiniteProjectiveGradedAlgebra.of
      (baerSumPullbackCarrier Λ P x y) (baerSumPullbackGrading Λ P x y))

/-- The base of `baerSumPullbackObj` is the dual-number self-pullback. -/
theorem baerSumPullbackObj_base (P : FiniteProjectiveGradedAlgebra k)
    (x y : (deformationForget Λ P).Fiber (dualNumber Λ k)) :
    (baerSumPullbackObj Λ P x y).base = dualNumberSelfPullback Λ := sorry

/-- The reduction `Q ×_P R → P` of the fibre-product algebra, as a graded ring map. -/
def baerSumPullbackGradedHom (P : FiniteProjectiveGradedAlgebra k)
    (x y : (deformationForget Λ P).Fiber (dualNumber Λ k)) :
    baerSumPullbackGrading Λ P x y →+*ᵍ P.grading where
  toRingHom :=
    (reductionRingHom Λ P x).comp
      (RingHom.pullbackFst (reductionRingHom Λ P x) (reductionRingHom Λ P y))
  map_mem := sorry

/-- The underlying ring map of `baerSumPullbackGradedHom` is the first pullback projection
followed by the reduction of `x`. -/
theorem baerSumPullbackGradedHom_toRingHom (P : FiniteProjectiveGradedAlgebra k)
    (x y : (deformationForget Λ P).Fiber (dualNumber Λ k)) :
    (baerSumPullbackGradedHom Λ P x y).toRingHom =
      (reductionRingHom Λ P x).comp
        (RingHom.pullbackFst (reductionRingHom Λ P x) (reductionRingHom Λ P y)) := sorry

/-- The morphism `(k[ε] ×_k k[ε], Q ×_P R) ⟶ (k, P)` over the coefficient projection. -/
def baerSumPullbackToResidue (P : FiniteProjectiveGradedAlgebra k)
    (x y : (deformationForget Λ P).Fiber (dualNumber Λ k)) :
    baerSumPullbackObj Λ P x y ⟶ ofResidue Λ P :=
  Hom.of (dualNumberSelfPullbackToResidue Λ) (baerSumPullbackGradedHom Λ P x y) sorry sorry

/-- `baerSumPullbackToResidue` has base arrow `dualNumberSelfPullbackToResidue`. -/
theorem baerSumPullbackToResidue_baseHom (P : FiniteProjectiveGradedAlgebra k)
    (x y : (deformationForget Λ P).Fiber (dualNumber Λ k)) :
    (baerSumPullbackToResidue Λ P x y).baseHom =
      dualNumberSelfPullbackToResidue Λ := sorry

/-- The Rim–Schlessinger fibre product of two dual-number fibre objects of `Def_P`, as the
graded algebra pullback of their underlying algebras along the reductions to `P`, lying over
`k[ε] ×_k k[ε]`. -/
def baerSumPullback (P : FiniteProjectiveGradedAlgebra k)
    (x y : (deformationForget Λ P).Fiber (dualNumber Λ k)) :
    Over (Fiber.fiberInclusion.obj (residueObj Λ P)) :=
  Over.mk (baerSumPullbackToResidue Λ P x y)

/-- `baerSumPullback` is the over-object of `baerSumPullbackToResidue`. -/
theorem baerSumPullback_eq (P : FiniteProjectiveGradedAlgebra k)
    (x y : (deformationForget Λ P).Fiber (dualNumber Λ k)) :
    baerSumPullback Λ P x y = Over.mk (baerSumPullbackToResidue Λ P x y) := sorry

/-- The fibre-product object of `Def_P` over `k[ε] ×_k k[ε]`. -/
def baerSumPullbackFiber (P : FiniteProjectiveGradedAlgebra k)
    (x y : (deformationForget Λ P).Fiber (dualNumber Λ k)) :
    (deformationForget Λ P).Fiber (dualNumberSelfPullback Λ) :=
  Fiber.mk
    (rfl : (deformationForget Λ P).obj (baerSumPullback Λ P x y) = dualNumberSelfPullback Λ)

/-- `baerSumPullbackFiber` is the fibre object associated to `baerSumPullback`. -/
theorem baerSumPullbackFiber_eq (P : FiniteProjectiveGradedAlgebra k)
    (x y : (deformationForget Λ P).Fiber (dualNumber Λ k)) :
    baerSumPullbackFiber Λ P x y =
      Fiber.mk
        (rfl : (deformationForget Λ P).obj (baerSumPullback Λ P x y) =
          dualNumberSelfPullback Λ) := sorry

/-- Baer sum of dual-number fibre objects: form the graded algebra fibre product over `x0`
and push forward along dual-number addition. -/
def baerSumFiber (P : FiniteProjectiveGradedAlgebra k)
    (x y : (deformationForget Λ P).Fiber (dualNumber Λ k)) :
    (deformationForget Λ P).Fiber (dualNumber Λ k) :=
  pushforwardFiberObj (deformationForget Λ P) (cleavageOp (deformationForget Λ P))
    (dualNumberAddHom Λ) (baerSumPullbackFiber Λ P x y)

/-- `baerSumFiber` is the pushforward of the (RS) fibre product along dual-number addition. -/
theorem baerSumFiber_spec (P : FiniteProjectiveGradedAlgebra k)
    (x y : (deformationForget Λ P).Fiber (dualNumber Λ k)) :
    baerSumFiber Λ P x y =
      pushforwardFiberObj (deformationForget Λ P) (cleavageOp (deformationForget Λ P))
        (dualNumberAddHom Λ) (baerSumPullbackFiber Λ P x y) := sorry

/-- Addition of tangent vectors by Baer sum of dual-number fibre classes. -/
def addTangent (P : FiniteProjectiveGradedAlgebra k) :
    tangentSpace (deformationForget Λ P) →
      tangentSpace (deformationForget Λ P) →
      tangentSpace (deformationForget Λ P) :=
  Quotient.lift₂
    (fun x y ↦ tangentSpace.mk (deformationForget Λ P) (baerSumFiber Λ P x y))
    (fun _ _ _ _ _ _ ↦ sorry)

/-- `addTangent` on represented classes is the class of `baerSumFiber`. -/
theorem addTangent_eq (P : FiniteProjectiveGradedAlgebra k)
    (x y : (deformationForget Λ P).Fiber (dualNumber Λ k)) :
    addTangent Λ P (tangentSpace.mk (deformationForget Λ P) x)
        (tangentSpace.mk (deformationForget Λ P) y) =
      tangentSpace.mk (deformationForget Λ P) (baerSumFiber Λ P x y) := sorry

/-- Scalar multiplication on `T Def_P` by dual-number pushforward along `ε ↦ c ε`. -/
def smulTangent (P : FiniteProjectiveGradedAlgebra k) (c : k)
    (x : tangentSpace (deformationForget Λ P)) :
    tangentSpace (deformationForget Λ P) :=
  (pushforwardFiberFunctor (deformationForget Λ P) (cleavageOp (deformationForget Λ P))
      (dualNumberScaleHom Λ c)).isoClassesMap x

/-- `smulTangent` is pushforward of isomorphism classes along dual-number scaling. -/
theorem smulTangent_eq (P : FiniteProjectiveGradedAlgebra k) (c : k)
    (x : tangentSpace (deformationForget Λ P)) :
    smulTangent Λ P c x =
      (pushforwardFiberFunctor (deformationForget Λ P)
          (cleavageOp (deformationForget Λ P))
          (dualNumberScaleHom Λ c)).isoClassesMap x := sorry

/-- Zero tangent vector, as the class of the trivial deformation `P[ε]`. -/
instance instZero_tangentSpace (P : FiniteProjectiveGradedAlgebra k) :
    Zero (tangentSpace (deformationForget Λ P)) where
  zero := tangentSpace.mk (deformationForget Λ P) (trivialDeformationFiber Λ P)

/-- Addition of tangent vectors. -/
instance instAdd_tangentSpace (P : FiniteProjectiveGradedAlgebra k) :
    Add (tangentSpace (deformationForget Λ P)) where
  add := addTangent Λ P

/-- Negation of tangent vectors by scaling with `-1`. -/
instance instNeg_tangentSpace (P : FiniteProjectiveGradedAlgebra k) :
    Neg (tangentSpace (deformationForget Λ P)) where
  neg x := smulTangent Λ P (-1) x

/-- Additive group structure on `T Def_P`, with Baer sum as addition. -/
instance instAddCommGroup_tangentSpace (P : FiniteProjectiveGradedAlgebra k) :
    AddCommGroup (tangentSpace (deformationForget Λ P)) where
  add_assoc := sorry
  zero_add := sorry
  add_zero := sorry
  nsmul := nsmulRec
  nsmul_zero := sorry
  nsmul_succ := sorry
  sub_eq_add_neg := sorry
  zsmul := zsmulRec
  zsmul_zero' := sorry
  zsmul_succ' := sorry
  zsmul_neg' := sorry
  neg_add_cancel := sorry
  add_comm := sorry

/-- `T Def_P` is a `k`-vector space, with scalars acting by dual-number pushforward. -/
instance instModule_tangentSpace (P : FiniteProjectiveGradedAlgebra k) :
    Module k (tangentSpace (deformationForget Λ P)) where
  smul := smulTangent Λ P
  one_smul := sorry
  zero_smul := sorry
  smul_zero := sorry
  smul_add := sorry
  add_smul := sorry
  mul_smul := sorry

/-- Lemma 93.7.3 (1)
In Example 93.7.1, `Inf(Def_P)` is the group of fibre automorphisms of the trivial
deformation `P[ε]`, and the comparison `γ = id + ε D` identifies it with the space
`Der_k(P, P)` of homogeneous degree-0 `k`-derivations `P → P`. -/
@[stacks 0DVZ]
theorem inf_bijective_homogeneousDerivations (P : FiniteProjectiveGradedAlgebra k) :
    Function.Bijective (idAddEpsilon Λ P) := sorry

/-- Lemma 93.7.3 (2)
If `P` is finitely generated as a `k`-algebra, then the space of homogeneous degree-0
`k`-derivations `P → P` is a finite-dimensional `k`-vector space. -/
@[stacks 0DVZ]
theorem homogeneousDerivations_finiteDimensional (P : FiniteProjectiveGradedAlgebra k)
    [Algebra.FiniteType k P.carrier] :
    FiniteDimensional k (homogeneousDerivations P.grading) := sorry

/-- Lemma 93.7.3 (3)
If `P` is finitely generated as a `k`-algebra, then `T Def_P` is a finite-dimensional
`k`-vector space. -/
@[stacks 0DVZ]
theorem tangentSpace_finiteDimensional (P : FiniteProjectiveGradedAlgebra k)
    [Algebra.FiniteType k P.carrier] :
    FiniteDimensional k (tangentSpace (deformationForget Λ P)) := sorry

end

end FiniteProjectiveGradedAlgebraCat
