/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalDeformation.Groupoid.CoyonedaPresentation
public import ReasLib.AlgebraicGeometry.FormalDeformation.Predeformation.Bundled
public import ReasLib.AlgebraicGeometry.AlgebraicStack.FieldValuedPoint.Fiber
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Deformation
public import ReasLib.AlgebraicGeometry.AlgebraicStack.VersalRing
public import ReasLib.AlgebraicGeometry.AlgebraicStack.VersalRing.Existence
public import ReasLib.AlgebraicGeometry.FormalDeformation.CompleteLocal.Pushout
public import ReasLib.AlgebraicGeometry.FormalDeformation.SmoothPowerSeries
public import ReasLib.AlgebraicGeometry.FormalDeformation.Groupoid.Presentation
public import ReasLib.AlgebraicGeometry.FormalDeformation.FormalObject.Existence

/-! # Versal cogroupoid presentations at field-valued points -/

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
  [stack : AlgebraicStack X]
  [finiteType : AlgebraicStack.LocallyOfFiniteType (baseProjection.{u + 1, u, u + 1} X)]
  (x0 : FieldValuedPoint X)
  [pointFiniteType : AlgebraicGeometry.LocallyOfFiniteType x0.structureHom]
  {Λ : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Algebra Λ x0.K]
  [Module.Finite Λ x0.K]
  (openImmersion : Spec (CommRingCat.of Λ) ⟶ S)
  [IsOpenImmersion openImmersion]
  (h_factor :
    Spec.map (CommRingCat.ofHom (algebraMap Λ x0.K)) ≫ openImmersion =
      x0.structureHom)

/-- Hom-universe lift of the predeformation projection, matching `FormalObject`. -/
abbrev predeformationLiftProjection :
    ULiftHom.{u + 1} (bundled openImmersion x0.structureHom h_factor X x0.fiberObj).total ⥤
      ArtinianLocalAlgCat Λ x0.K :=
  ULiftHom.down ⋙ (bundled openImmersion x0.structureHom h_factor X x0.fiberObj).p

omit stack finiteType in
/-- `predeformationLiftProjection` is `ULiftHom.down` followed by the predeformation
projection. -/
theorem predeformationLiftProjection_eq :
    predeformationLiftProjection x0 openImmersion h_factor =
      ULiftHom.down ⋙ (bundled openImmersion x0.structureHom h_factor X x0.fiberObj).p :=
  rfl

include stack finiteType in
/-- At a finite-type field-valued point of an algebraic stack locally of finite type
over a locally Noetherian scheme, `ℱ_{X, k, x0}` admits a presentation by a
smooth prorepresentable groupoid in functors on `ArtinianLocalAlgCat Λ k`. -/
theorem exists_smoothProrepresentablePresentation :
    ∃ (G : GroupoidInFunctors.{u + 1, u, u} (ArtinianLocalAlgCat Λ x0.K))
      (φ : G.quotient ⟶ bundled openImmersion x0.structureHom h_factor X x0.fiberObj),
      GroupoidInFunctors.IsSmooth G.s G.t ∧ GroupoidInFunctors.IsProrepresentable G ∧
        GroupoidInFunctors.IsPresentation G (bundled openImmersion x0.structureHom h_factor X x0.fiberObj) φ :=
  sorry

include stack finiteType in
/-- Unwinding the presentation, one may choose a Noetherian
complete local `Λ`-algebra `A` with residue field `k` and a versal formal object
`ξ` of `ℱ_{X, k, x0}` over `A`. -/
theorem exists_versalFormalObject :
    ∃ ξ : _root_.FormalObject (predeformationLiftProjection x0 openImmersion h_factor),
      _root_.FormalObject.IsVersal ξ :=
  sorry

include stack finiteType in
/-- Given a versal formal object `ξ` over `A`, there is a
Noetherian complete local `Λ`-algebra `B` with residue field `k` and an isomorphism
`restrictedCoyoneda B ≅ relation (associatedMorphismOver ξ)` whose projections are
the restricted coyoneda maps of formally smooth morphisms `s, t : A ⟶ B` (in the
sense of `IsPowerSeriesOver`). -/
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

include stack finiteType in
/-- Given a versal formal object `ξ` and a kernel-pair algebra
`B` with formally smooth projections `s, t : A ⟶ B`, there is a
composition `c : B ⟶ pushout s t` making `(A, B, s, t, c)` a coyoneda cogroupoid
in `CompleteLocalAlgCat Λ k`, whose restriction along
`ArtinianLocalAlgCat.inclusion` is isomorphic to `ofFormalObject ξ`. -/
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
      (ε : GroupoidInFunctors.Iso
        (restrictInclusion (ofCoyoneda s t c idMap invMap laws))
        (ofFormalObject ξ)),
      ε.hom.obj = 𝟙 _ ∧ ε.hom.arrow = e.hom :=
  sorry

include stack finiteType in
/-- A versal formal object `ξ` induces an equivalence
`[restrictedCoyoneda A / relation (associatedMorphismOver ξ)] ⟶ ℱ_{X, k, x0}` of
groupoids cofibered over `ArtinianLocalAlgCat Λ k`. -/
theorem isPresentation_restrict
    (ξ : _root_.FormalObject (predeformationLiftProjection x0 openImmersion h_factor))
    [_root_.FormalObject.IsVersal ξ] :
    BasedFunctor.IsEquivalence
      (quotientMap (_root_.FormalObject.associatedMorphismOver ξ)) :=
  sorry

/-- The completion `hat(ℱ_{X, k, x0})` of the predeformation functor, as a based
category over `CompleteLocalAlgCat Λ k`. `Functor.completion` is only defined
when Hom and object universes agree, so this is the completion of the
Hom-universe lift `predeformationLiftProjection`. -/
noncomputable def predeformationHat :
    BasedCategory.{u + 1, u + 1} (CompleteLocalAlgCat Λ x0.K) :=
  BasedCategory.ofFunctor
    (Functor.completion (predeformationLiftProjection x0 openImmersion h_factor))

omit stack finiteType in
/-- The projection of `predeformationHat` is the completion of
`predeformationLiftProjection`. -/
theorem predeformationHat_p :
    (predeformationHat x0 openImmersion h_factor).p =
      Functor.completion (predeformationLiftProjection x0 openImmersion h_factor) :=
  rfl

include stack finiteType in
/-- The coyoneda cogroupoid with its supplied
restriction isomorphism to the kernel-pair groupoid of the same versal `ξ`,
presents `hat(ℱ_{X, k, x0})` over `CompleteLocalAlgCat Λ k`. The domain is the
actual quotient `[underline(A) / underline(B)]`. Completion of the supplied
isomorphism and the canonical completion–restriction comparison transport the
presentation; no definitional equality of groupoids is asserted.
The codomain `predeformationHat` retains the Hom-universe-lift model. -/
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
    BasedFunctor.IsEquivalence (coyonedaQuotientMap ξ e) :=
  sorry

section ForgetMarkings

omit stack finiteType [IsLocallyNoetherian S] [IsOpenImmersion openImmersion]

include pointFiniteType h_factor in
/-- The chosen residue identification and factorization through the affine chart
make the residue point of any complete local algebra locally of finite type. -/
theorem toSAlgebraOfBase_residue_locallyOfFiniteType (base : CompleteLocalAlgCat Λ x0.K) :
    LocallyOfFiniteType
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (maximalIdeal base.carrier))) ≫
        Spec.map (CommRingCat.ofHom (algebraMap Λ base.carrier)) ≫ openImmersion) :=
  sorry

/-- Forget the scalar and residue markings through the specified affine chart,
retaining the ring and its actual structure map to `S`. -/
def toSAlgebraOfBase (base : CompleteLocalAlgCat Λ x0.K) : CompleteLocalSAlgebra S :=
  CompleteLocalSAlgebra.of base.carrier
    (Spec.map (CommRingCat.ofHom (algebraMap Λ base.carrier)) ≫ openImmersion)
    (toSAlgebraOfBase_residue_locallyOfFiniteType x0 openImmersion h_factor base)

/-- The forgotten object has exactly the original carrier. -/
theorem toSAlgebraOfBase_carrier (base : CompleteLocalAlgCat Λ x0.K) :
    (toSAlgebraOfBase x0 openImmersion h_factor base).carrier = base.carrier := rfl

/-- The structure map is induced by the stored scalar action and chosen chart. -/
theorem toSAlgebraOfBase_toS (base : CompleteLocalAlgCat Λ x0.K) :
    (toSAlgebraOfBase x0 openImmersion h_factor base).toS =
      Spec.map (CommRingCat.ofHom (algebraMap Λ base.carrier)) ≫ openImmersion := rfl

/-- A marked algebra map gives the same ring map over `S`, with the contravariant
convention of `CompleteLocalSAlgebra.Hom`. -/
def toSAlgebraHom {source target : CompleteLocalAlgCat Λ x0.K} (map : source ⟶ target) :
    CompleteLocalSAlgebra.Hom
      (toSAlgebraOfBase x0 openImmersion h_factor target)
      (toSAlgebraOfBase x0 openImmersion h_factor source) where
  hom := map.toRingHom
  isLocalHom := ⟨map.isLocalHom.map_nonunit⟩
  over_S := by
    change Spec.map (CommRingCat.ofHom map.toRingHom) ≫
      (Spec.map (CommRingCat.ofHom (algebraMap Λ source.carrier)) ≫ openImmersion) =
        Spec.map (CommRingCat.ofHom (algebraMap Λ target.carrier)) ≫ openImmersion
    have hscalar : CommRingCat.ofHom (algebraMap Λ source.carrier) ≫
        CommRingCat.ofHom map.toRingHom = CommRingCat.ofHom (algebraMap Λ target.carrier) := by
      ext scalar
      exact map.hom.commutes scalar
    rw [← Category.assoc, ← Spec.map_comp, hscalar]

/-- Forgetting markings retains the underlying ring map definitionally. -/
theorem toSAlgebraHom_hom {source target : CompleteLocalAlgCat Λ x0.K} (map : source ⟶ target) :
    (toSAlgebraHom x0 openImmersion h_factor map).hom = map.toRingHom := rfl

/-- Forgetting a marked identity gives the geometric identity. -/
theorem toSAlgebraHom_id (base : CompleteLocalAlgCat Λ x0.K) :
    toSAlgebraHom x0 openImmersion h_factor (𝟙 base) =
      CompleteLocalSAlgebra.Hom.id (toSAlgebraOfBase x0 openImmersion h_factor base) := rfl

/-- Forgetting composition respects the contravariant geometric convention. -/
theorem toSAlgebraHom_comp {source middle target : CompleteLocalAlgCat Λ x0.K}
    (first : source ⟶ middle) (second : middle ⟶ target) :
    toSAlgebraHom x0 openImmersion h_factor (first ≫ second) =
      (toSAlgebraHom x0 openImmersion h_factor second).comp
        (toSAlgebraHom x0 openImmersion h_factor first) := rfl

/-- The geometric projection of the forgotten map is its actual spectrum map. -/
theorem toSAlgebraHom_toSpec {source target : CompleteLocalAlgCat Λ x0.K} (map : source ⟶ target) :
    (toSAlgebraHom x0 openImmersion h_factor map).toSpec =
      Spec.map (CommRingCat.ofHom map.toRingHom) := rfl

/-- On maps with the specified scalar and residue compatibility, the geometric
and marked power-series properties are the same coefficient-inclusion property. -/
theorem isPowerSeriesExtension_toSAlgebraHom_iff
    {source target : CompleteLocalAlgCat Λ x0.K} (map : source ⟶ target) :
    AlgebraicStack.IsPowerSeriesExtension (toSAlgebraHom x0 openImmersion h_factor map) ↔
      IsPowerSeriesOver map :=
  (isPowerSeriesOver_iff_toRingHom map).symm

end ForgetMarkings

/-- The residue-field morphism of `ξ.base` over `S` is locally of finite type. -/
theorem toSAlgebra_residue_locallyOfFiniteType
    (ξ : _root_.FormalObject (predeformationLiftProjection x0 openImmersion h_factor)) :
    LocallyOfFiniteType
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (maximalIdeal ξ.base.carrier))) ≫
        Spec.map (CommRingCat.ofHom (algebraMap Λ ξ.base.carrier)) ≫ openImmersion) :=
  toSAlgebraOfBase_residue_locallyOfFiniteType x0 openImmersion h_factor ξ.base

/-- The complete local `S`-algebra with carrier `ξ.base.carrier` and structure
morphism `Spec.map (algebraMap Λ ξ.base.carrier) ≫ openImmersion`. -/
def toSAlgebra
    (ξ : _root_.FormalObject (predeformationLiftProjection x0 openImmersion h_factor)) :
    CompleteLocalSAlgebra S :=
  toSAlgebraOfBase x0 openImmersion h_factor ξ.base

/-- The carrier of `toSAlgebra ξ` is the underlying ring of `ξ.base`. -/
theorem toSAlgebra_carrier
    (ξ : _root_.FormalObject (predeformationLiftProjection x0 openImmersion h_factor)) :
    (toSAlgebra x0 openImmersion h_factor ξ).carrier = ξ.base.carrier :=
  rfl

/-- The structure morphism of `toSAlgebra ξ` is
`Spec.map (algebraMap Λ ξ.base.carrier) ≫ openImmersion`. -/
theorem toSAlgebra_toS
    (ξ : _root_.FormalObject (predeformationLiftProjection x0 openImmersion h_factor)) :
    (toSAlgebra x0 openImmersion h_factor ξ).toS =
      Spec.map (CommRingCat.ofHom (algebraMap Λ ξ.base.carrier)) ≫ openImmersion :=
  rfl

include stack finiteType in
/-- The complete local `Λ`-algebra `A` underlying a versal
formal object of `ℱ_{X, k, x0}` is a versal ring to `X` at `x0`. -/
instance instIsVersalRing_toSAlgebra
    (ξ : _root_.FormalObject (predeformationLiftProjection x0 openImmersion h_factor))
    [_root_.FormalObject.IsVersal ξ] :
    AlgebraicStack.IsVersalRing x0 (toSAlgebra x0 openImmersion h_factor ξ) :=
  sorry

include stack finiteType in
/-- A finite-type field-valued point of a locally finite type algebraic stack has a
smooth prorepresentable presentation and a compatible versal coyoneda cogroupoid
whose induced restricted and completed quotient maps are equivalences. Its object
algebra is a versal ring at the given point. -/
theorem exists_versalCogroupoidPresentation :
    (∃ (G : GroupoidInFunctors.{u + 1, u, u} (ArtinianLocalAlgCat Λ x0.K))
      (φ : G.quotient ⟶ bundled openImmersion x0.structureHom h_factor X x0.fiberObj),
      GroupoidInFunctors.IsSmooth G.s G.t ∧ GroupoidInFunctors.IsProrepresentable G ∧
        GroupoidInFunctors.IsPresentation G
          (bundled openImmersion x0.structureHom h_factor X x0.fiberObj) φ) ∧
    ∃ (ξ : _root_.FormalObject (predeformationLiftProjection x0 openImmersion h_factor))
      (B : CompleteLocalAlgCat Λ x0.K) (s t : ξ.base ⟶ B)
      (e : restrictedCoyoneda B ≅ relation (_root_.FormalObject.associatedMorphismOver ξ))
      (c : B ⟶ pushout s t)
      (idMap : coyoneda.obj (op ξ.base) ⟶ coyoneda.obj (op B))
      (invMap : coyoneda.obj (op B) ⟶ coyoneda.obj (op B))
      (laws : CoyonedaGroupoidLaws s t c idMap invMap)
      (ε : GroupoidInFunctors.Iso
        (restrictInclusion (ofCoyoneda s t c idMap invMap laws)) (ofFormalObject ξ)),
      _root_.FormalObject.IsVersal ξ ∧
      e.hom ≫ src (_root_.FormalObject.associatedMorphismOver ξ) = restrictedCoyonedaMap s ∧
      e.hom ≫ tgt (_root_.FormalObject.associatedMorphismOver ξ) = restrictedCoyonedaMap t ∧
      IsPowerSeriesOver s ∧ IsPowerSeriesOver t ∧
      ε.hom.obj = 𝟙 _ ∧ ε.hom.arrow = e.hom ∧
      BasedFunctor.IsEquivalence (quotientMap (_root_.FormalObject.associatedMorphismOver ξ)) ∧
      BasedFunctor.IsEquivalence (coyonedaQuotientMap ξ ε) ∧
      AlgebraicStack.IsVersalRing x0 (toSAlgebra x0 openImmersion h_factor ξ) :=
  sorry

end AlgebraicGeometry.GroupoidsOver.Predeformation
