module

public import Mathlib.CategoryTheory.Category.ULift
public import stacks_project.Chap90.Definition_90_21_4_Functors
public import stacks_project.Chap90.Definition_90_22_2_Completion
public import stacks_project.Chap90.Lemma_90_4_3
public import stacks_project.Chap90.Lemma_90_8_6_Coyoneda
public import stacks_project.Chap90.Lemma_90_8_6_PowerSeries
public import stacks_project.Chap90.Lemma_90_25_2
public import stacks_project.Chap90.Lemma_90_26_1
public import stacks_project.Chap90.Lemma_90_27_6_Presentation
public import stacks_project.Chap90.Definition_90_7_3
public import stacks_project.Chap90.Theorem_90_26_4
public import stacks_project.Chap107.Definition_107_4_1_VersalRing
public import stacks_project.Chap107.Lemma_107_2_3
import Mathlib.Tactic.CrossRefAttribute

/-!
# Smooth prorepresentable presentations of predeformation functors

In Situation 107.2.1, the predeformation functor `ℱ_{X, k, x0}` of a finite-type
field-valued point admits a presentation by a smooth prorepresentable groupoid in
functors on `ArtinianLocalAlgCat Λ k`. Unwinding that presentation yields a versal
formal object, a formally smooth kernel pair, a coyoneda cogroupoid, equivalences
after restriction and completion, and a versal ring.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits Opposite IsLocalRing
open AlgebraicGeometry.AlgebraicStack (FieldValuedPoint)
open FiberedCategoryOver.Groupoids
open CompleteLocalAlgCat
open GroupoidInFunctors
open scoped Bicategory BasedFunctor

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver.Predeformation

variable {S : Scheme.{u}} [IsLocallyNoetherian S] {X : GroupoidsOver S}
  [AlgebraicStack X]
  [AlgebraicStack.LocallyOfFiniteType (baseProjection.{u + 1, u, u + 1} X)]
  (x0 : FieldValuedPoint X)
  [AlgebraicGeometry.LocallyOfFiniteType x0.structureHom]
  {Λ : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Algebra Λ x0.K]
  [Module.Finite Λ x0.K]
  (openImmersion : Spec (CommRingCat.of Λ) ⟶ S)
  [IsOpenImmersion openImmersion]
  (h_factor :
    Spec.map (CommRingCat.ofHom (algebraMap Λ x0.K)) ≫ openImmersion =
      x0.structureHom)

/-- The predeformation category `ℱ_{X, k, x0}` as a category cofibered in groupoids
over `ArtinianLocalAlgCat Λ k`. -/
abbrev predeformationGroupoids :
    CofiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u}
      (ArtinianLocalAlgCat Λ x0.K) :=
  CofiberedCategoryOver.Groupoids.ofFunctor
    (predeformationFunctor X openImmersion x0.structureHom h_factor x0.fiberObj)

/-- The projection of `predeformationGroupoids` is the predeformation functor. -/
theorem predeformationGroupoids_p :
    (predeformationGroupoids x0 openImmersion h_factor).p =
      predeformationFunctor X openImmersion x0.structureHom h_factor x0.fiberObj :=
  sorry

/-- Hom-universe lift of the predeformation projection, matching `FormalObject`. -/
abbrev predeformationLiftProjection :
    ULiftHom.{u + 1} (predeformationGroupoids x0 openImmersion h_factor).total ⥤
      ArtinianLocalAlgCat Λ x0.K :=
  ULiftHom.down ⋙ (predeformationGroupoids x0 openImmersion h_factor).p

/-- `predeformationLiftProjection` is `ULiftHom.down` followed by the predeformation
projection. -/
theorem predeformationLiftProjection_eq :
    predeformationLiftProjection x0 openImmersion h_factor =
      ULiftHom.down ⋙ (predeformationGroupoids x0 openImmersion h_factor).p :=
  sorry

/-- Remark 107.2.11 (1): In Situation 107.2.1, if `x0 : Spec(k) ⟶ X` is a morphism
with `k` of finite type over `S`, then `ℱ_{X, k, x0}` admits a presentation by a
smooth prorepresentable groupoid in functors on `ArtinianLocalAlgCat Λ k`. -/
@[stacks 0DR3]
theorem exists_smoothProrepresentablePresentation :
    ∃ (G : GroupoidInFunctors.{u + 1, u, u} (ArtinianLocalAlgCat Λ x0.K))
      (φ : G.quotient ⟶ predeformationGroupoids x0 openImmersion h_factor),
      GroupoidInFunctors.IsSmooth G.s G.t ∧ GroupoidInFunctors.IsProrepresentable G ∧
        GroupoidInFunctors.IsPresentation G (predeformationGroupoids x0 openImmersion h_factor) φ :=
  sorry

/-- Remark 107.2.11 (2): Unwinding the presentation, one may choose a Noetherian
complete local `Λ`-algebra `A` with residue field `k` and a versal formal object
`ξ` of `ℱ_{X, k, x0}` over `A`. -/
@[stacks 0DR3]
theorem exists_versalFormalObject :
    ∃ ξ : _root_.FormalObject (predeformationLiftProjection x0 openImmersion h_factor),
      _root_.FormalObject.IsVersal ξ :=
  sorry

/-- Remark 107.2.11 (3): Given a versal formal object `ξ` over `A`, there is a
Noetherian complete local `Λ`-algebra `B` with residue field `k` and an isomorphism
`restrictedCoyoneda B ≅ relation (associatedMorphismOver ξ)` whose projections are
the restricted coyoneda maps of formally smooth morphisms `s, t : A ⟶ B` (in the
sense of `IsPowerSeriesOver`). -/
@[stacks 0DR3]
theorem exists_kernelPairAlgebra
    (ξ : _root_.FormalObject (predeformationLiftProjection x0 openImmersion h_factor))
    [_root_.FormalObject.IsVersal ξ] :
    ∃ (B : CompleteLocalAlgCat Λ x0.K) (s t : ξ.base ⟶ B)
      (e : restrictedCoyoneda B ≅
        relation (_root_.FormalObject.associatedMorphismOver ξ)),
      e.hom ≫ src (_root_.FormalObject.associatedMorphismOver ξ) =
          restrictedCoyonedaMap s ∧
        e.hom ≫ tgt (_root_.FormalObject.associatedMorphismOver ξ) =
          restrictedCoyonedaMap t ∧
        IsPowerSeriesOver s ∧ IsPowerSeriesOver t :=
  sorry

/-- Remark 107.2.11 (4): Given a versal formal object `ξ` and a kernel-pair algebra
`B` with formally smooth projections `s, t : A ⟶ B` as in (3), there is a
composition `c : B ⟶ pushout s t` making `(A, B, s, t, c)` a coyoneda cogroupoid
in `CompleteLocalAlgCat Λ k`, whose restriction along
`ArtinianLocalAlgCat.inclusion` is isomorphic to `ofFormalObject ξ`. -/
@[stacks 0DR3]
theorem exists_cogroupoidComp
    (ξ : _root_.FormalObject (predeformationLiftProjection x0 openImmersion h_factor))
    [_root_.FormalObject.IsVersal ξ]
    (B : CompleteLocalAlgCat Λ x0.K) (s t : ξ.base ⟶ B)
    (e : restrictedCoyoneda B ≅ relation (_root_.FormalObject.associatedMorphismOver ξ))
    (h_src :
      e.hom ≫ src (_root_.FormalObject.associatedMorphismOver ξ) = restrictedCoyonedaMap s)
    (h_tgt :
      e.hom ≫ tgt (_root_.FormalObject.associatedMorphismOver ξ) = restrictedCoyonedaMap t)
    (hs : IsPowerSeriesOver s) (ht : IsPowerSeriesOver t) :
    ∃ (c : B ⟶ pushout s t)
      (idMap : coyoneda.obj (op ξ.base) ⟶ coyoneda.obj (op B))
      (invMap : coyoneda.obj (op B) ⟶ coyoneda.obj (op B))
      (laws : CoyonedaGroupoidLaws s t c idMap invMap)
      (e : GroupoidInFunctors.Iso
        (restrictInclusion (ofCoyoneda s t c idMap invMap laws))
        (ofFormalObject ξ)),
      True :=
  sorry

/-- Remark 107.2.11 (5): A versal formal object `ξ` induces an equivalence
`[restrictedCoyoneda A / relation (associatedMorphismOver ξ)] ⟶ ℱ_{X, k, x0}` of
groupoids cofibered over `ArtinianLocalAlgCat Λ k`. -/
@[stacks 0DR3]
theorem isPresentation_restrict
    (ξ : _root_.FormalObject (predeformationLiftProjection x0 openImmersion h_factor))
    [_root_.FormalObject.IsVersal ξ] :
    ∃ φ : (ofFormalObject ξ).quotient ⟶
        predeformationGroupoids x0 openImmersion h_factor,
      GroupoidInFunctors.IsPresentation (ofFormalObject ξ)
        (predeformationGroupoids x0 openImmersion h_factor) φ :=
  sorry

/-- The completion `hat(ℱ_{X, k, x0})` of the predeformation functor, as a based
category over `CompleteLocalAlgCat Λ k`. `Functor.completion` is only defined
when Hom and object universes agree, so this is the completion of the
Hom-universe lift `predeformationLiftProjection`. -/
noncomputable def predeformationHat :
    BasedCategory.{u + 1, u + 1} (CompleteLocalAlgCat Λ x0.K) :=
  BasedCategory.ofFunctor
    (Functor.completion (predeformationLiftProjection x0 openImmersion h_factor))

/-- The projection of `predeformationHat` is the completion of
`predeformationLiftProjection`. -/
theorem predeformationHat_p :
    (predeformationHat x0 openImmersion h_factor).p =
      Functor.completion (predeformationLiftProjection x0 openImmersion h_factor) :=
  sorry

/-- `predeformationHat` is the based category of formal objects of the
Hom-universe lift of the predeformation projection. -/
theorem predeformationHat_eq :
    predeformationHat x0 openImmersion h_factor =
      BasedCategory.ofFunctor
        (Functor.completion (predeformationLiftProjection x0 openImmersion h_factor)) :=
  sorry

/-- Remark 107.2.11 (6): The coyoneda cogroupoid from (4), with its supplied
restriction isomorphism to the kernel-pair groupoid of the same versal `ξ`,
presents `hat(ℱ_{X, k, x0})` over `CompleteLocalAlgCat Λ k`. The domain is the
actual quotient `[underline(A) / underline(B)]`. Completion of the supplied
isomorphism and the canonical completion–restriction comparison transport the
presentation; no definitional equality of groupoids is asserted.
The codomain `predeformationHat` retains the Hom-universe-lift model. -/
@[stacks 0DR3]
theorem isPresentation_completion
    (ξ : _root_.FormalObject (predeformationLiftProjection x0 openImmersion h_factor))
    [_root_.FormalObject.IsVersal ξ]
    (B : CompleteLocalAlgCat Λ x0.K) (s t : ξ.base ⟶ B)
    (c : B ⟶ pushout s t)
    (idMap : coyoneda.obj (op ξ.base) ⟶ coyoneda.obj (op B))
    (invMap : coyoneda.obj (op B) ⟶ coyoneda.obj (op B))
    (laws : CoyonedaGroupoidLaws s t c idMap invMap)
    (e : GroupoidInFunctors.Iso
      (restrictInclusion (ofCoyoneda s t c idMap invMap laws)) (ofFormalObject ξ)) :
    ∃ φ :
      (ofCoyoneda s t c idMap invMap laws).quotient.toBasedCategory ⥤ᵇ
        predeformationHat x0 openImmersion h_factor,
      BasedFunctor.IsEquivalence φ :=
  sorry

/-- The residue-field morphism of `ξ.base` over `S` is locally of finite type. -/
theorem toSAlgebra_residue_locallyOfFiniteType
    (ξ : _root_.FormalObject (predeformationLiftProjection x0 openImmersion h_factor)) :
    LocallyOfFiniteType
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (maximalIdeal ξ.base.carrier))) ≫
        Spec.map (CommRingCat.ofHom (algebraMap Λ ξ.base.carrier)) ≫ openImmersion) :=
  sorry

/-- The complete local `S`-algebra with carrier `ξ.base.carrier` and structure
morphism `Spec.map (algebraMap Λ ξ.base.carrier) ≫ openImmersion`. -/
def toSAlgebra
    (ξ : _root_.FormalObject (predeformationLiftProjection x0 openImmersion h_factor)) :
    CompleteLocalSAlgebra S :=
  CompleteLocalSAlgebra.of ξ.base.carrier
    (Spec.map (CommRingCat.ofHom (algebraMap Λ ξ.base.carrier)) ≫ openImmersion)
    (toSAlgebra_residue_locallyOfFiniteType x0 openImmersion h_factor ξ)

/-- The carrier of `toSAlgebra ξ` is the underlying ring of `ξ.base`. -/
theorem toSAlgebra_carrier
    (ξ : _root_.FormalObject (predeformationLiftProjection x0 openImmersion h_factor)) :
    (toSAlgebra x0 openImmersion h_factor ξ).carrier = ξ.base.carrier :=
  sorry

/-- The structure morphism of `toSAlgebra ξ` is
`Spec.map (algebraMap Λ ξ.base.carrier) ≫ openImmersion`. -/
theorem toSAlgebra_toS
    (ξ : _root_.FormalObject (predeformationLiftProjection x0 openImmersion h_factor)) :
    (toSAlgebra x0 openImmersion h_factor ξ).toS =
      Spec.map (CommRingCat.ofHom (algebraMap Λ ξ.base.carrier)) ≫ openImmersion :=
  sorry

/-- Remark 107.2.11 (7): The complete local `Λ`-algebra `A` underlying a versal
formal object of `ℱ_{X, k, x0}` is a versal ring to `X` at `x0`. -/
@[stacks 0DR3, instance]
instance instIsVersalRing_toSAlgebra
    (ξ : _root_.FormalObject (predeformationLiftProjection x0 openImmersion h_factor))
    [_root_.FormalObject.IsVersal ξ] :
    AlgebraicStack.IsVersalRing x0 (toSAlgebra x0 openImmersion h_factor ξ) :=
  sorry

end AlgebraicGeometry.GroupoidsOver.Predeformation
