module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleLocalRing.Noetherian
public import ReasLib.Algebra.Homology.DerivedCategory.Dualizing.Normalized
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.Coextension
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Dualizing.NormalizationDegree
public import ReasLib.Topology.Specialization.Dimension
public import stacks_project.Chap65.Definition_65_13_2_Separation
public import stacks_project.Chap66.Lemma_66_24_4
public import stacks_project.Chap66.Lemma_66_4_6_Topology
public import stacks_project.Chap75.Lemma_75_26_3_FiberEulerCharacteristic
public import stacks_project.Chap86.Lemma_86_2_1_EtaleDualizing

/-!
# Normalization degree of a dualizing complex on an algebraic space

The integer function on `|X|` attached to a dualizing complex is the unique function whose
value at each point is the residue-field coextension degree of the derived étale stalk.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.ModuleDerived (geometricPointOver stalkDerived)
open AlgebraicGeometry.Scheme.DerivedQCoh (SmallEtale epsilonStar)

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.DerivedQCoh

/-- The derived étale stalk of `ω` at the chosen geometric point over `x`. -/
noncomputable def geometricStalk {S : Scheme.{u}} {X : AlgebraicSpace S}
    (ω : DerivedQCoh X) (x : Points X) :
    DerivedCategory (ModuleCat (etaleLocalRing X (geometricPointOver x))) :=
  stalkDerived (geometricPointOver x) ((inclusion X).obj ω)

/-- A function records the normalization degrees of the derived étale stalks of `ω` when its
value at each point is the shift of the residue field obtained by derived coextension. -/
def IsGeometricStalkNormalizationDegreeFunction {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsLocallyNoetherian X] (ω : DerivedQCoh X) (δ : Points X → ℤ) : Prop :=
  ∀ x : Points X,
    Nonempty
      ((ModuleCat.derivedCoextensionOfScalars
          (algebraMap (etaleLocalRing X (geometricPointOver x))
            (IsLocalRing.ResidueField (etaleLocalRing X (geometricPointOver x))))).obj
          (geometricStalk ω x) ≅
        (shiftFunctor
            (DerivedCategory
              (ModuleCat.{u}
                (IsLocalRing.ResidueField (etaleLocalRing X (geometricPointOver x)))))
            (δ x)).obj
          (ModuleCat.single0
            (ModuleCat.of
              (IsLocalRing.ResidueField (etaleLocalRing X (geometricPointOver x)))
              (IsLocalRing.ResidueField (etaleLocalRing X (geometricPointOver x))))))

/-- The residue-field characterization of a geometric-stalk normalization degree at a point. -/
theorem IsGeometricStalkNormalizationDegreeFunction.at {S : Scheme.{u}}
    {X : AlgebraicSpace S} [IsLocallyNoetherian X] {ω : DerivedQCoh X} {δ : Points X → ℤ}
    (hδ : IsGeometricStalkNormalizationDegreeFunction ω δ) (x : Points X) :
    Nonempty
      ((ModuleCat.derivedCoextensionOfScalars
          (algebraMap (etaleLocalRing X (geometricPointOver x))
            (IsLocalRing.ResidueField (etaleLocalRing X (geometricPointOver x))))).obj
          (geometricStalk ω x) ≅
        (shiftFunctor
            (DerivedCategory
              (ModuleCat.{u}
                (IsLocalRing.ResidueField (etaleLocalRing X (geometricPointOver x)))))
            (δ x)).obj
          (ModuleCat.single0
            (ModuleCat.of
              (IsLocalRing.ResidueField (etaleLocalRing X (geometricPointOver x)))
              (IsLocalRing.ResidueField (etaleLocalRing X (geometricPointOver x)))))) :=
  sorry

/-- The canonical normalization-degree function determined by a dualizing complex on a
locally Noetherian algebraic space, in the sense of `forallEtaleScheme`. -/
noncomputable def normalizationDegree {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsLocallyNoetherian X] {ω : DerivedQCoh X} (hω : forallEtaleScheme ω) : Points X → ℤ :=
  @dite (Points X → ℤ) (∃ δ : Points X → ℤ, IsGeometricStalkNormalizationDegreeFunction ω δ)
    (Classical.propDecidable _) (fun h ↦ Classical.choose h) (fun _ _ ↦ 0)

/-- The canonical normalization-degree function has the defining stalkwise property. -/
theorem normalizationDegree_spec {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsLocallyNoetherian X] {ω : DerivedQCoh X} (hω : forallEtaleScheme ω) :
    IsGeometricStalkNormalizationDegreeFunction ω (normalizationDegree hω) :=
  sorry

/-- Any geometric-stalk normalization-degree function of a fixed dualizing complex is the
canonical one. -/
theorem normalizationDegree_eq {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsLocallyNoetherian X] {ω : DerivedQCoh X} (hω : forallEtaleScheme ω) {δ : Points X → ℤ}
    (hδ : IsGeometricStalkNormalizationDegreeFunction ω δ) :
    δ = normalizationDegree hω :=
  sorry

/-- Shifting the derived étale stalk at the chosen geometric point over `x` by the negative
canonical normalization degree gives a normalized dualizing complex over the étale local
ring. -/
theorem normalizationDegree_stalkShift_isNormalized {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsLocallyNoetherian X] {ω : DerivedQCoh X} (hω : forallEtaleScheme ω)
    [monoidal : ∀ xbar : GeometricPoint X,
      MonoidalCategory (DerivedCategory (ModuleCat.{u} (etaleLocalRing X xbar)))]
    (H : ∀ xbar : GeometricPoint X, @MonoidalClosed _ inferInstance (monoidal xbar))
    (x : Points X) :
    -- Local instance justification (proof-local temporary data): IsNormalizedDualizingComplex requires the explicit canonical IsNoetherianRing proof as a class argument here; keep it local without registering a global companion instance.
    letI := etaleLocalRing.instIsNoetherianRing (geometricPointOver x)
    -- Local instance justification (proof-local temporary data): IsNormalizedDualizingComplex requires the explicit canonical IsLocalRing proof as a class argument here; keep it local without registering a global companion instance.
    letI := etaleLocalRing.instIsLocalRing (geometricPointOver x)
    ((shiftFunctor (DerivedCategory (ModuleCat.{u} (etaleLocalRing X (geometricPointOver x))))
          (-(normalizationDegree hω x))).obj
        (geometricStalk ω x)).IsNormalizedDualizingComplex (H (geometricPointOver x)) :=
  sorry

/-- If `xbar` lies over `x`, shifting the derived étale stalk at `xbar` by
`-(normalizationDegree hω x)` gives a normalized dualizing complex over
`etaleLocalRing X xbar`. -/
theorem normalizationDegree_stalkShift_isNormalized_of_liesOver {S : Scheme.{u}}
    {X : AlgebraicSpace S} [IsLocallyNoetherian X] {ω : DerivedQCoh X}
    (hω : forallEtaleScheme ω)
    [monoidal : ∀ xbar : GeometricPoint X,
      MonoidalCategory (DerivedCategory (ModuleCat.{u} (etaleLocalRing X xbar)))]
    (H : ∀ xbar : GeometricPoint X, @MonoidalClosed _ inferInstance (monoidal xbar))
    {x : Points X} {xbar : GeometricPoint X} (hx : xbar.image = x) :
    -- Local instance justification (proof-local temporary data): IsNormalizedDualizingComplex requires the explicit canonical IsNoetherianRing proof as a class argument here; keep it local without registering a global companion instance.
    letI := etaleLocalRing.instIsNoetherianRing xbar
    -- Local instance justification (proof-local temporary data): IsNormalizedDualizingComplex requires the explicit canonical IsLocalRing proof as a class argument here; keep it local without registering a global companion instance.
    letI := etaleLocalRing.instIsLocalRing xbar
    ((shiftFunctor (DerivedCategory (ModuleCat.{u} (etaleLocalRing X xbar)))
          (-(normalizationDegree hω x))).obj
        (stalkDerived xbar ((inclusion X).obj ω))).IsNormalizedDualizingComplex (H xbar) :=
  sorry

/-- Along an étale scheme chart, the algebraic-space normalization degree pulls back to the
scheme-level normalization degree of a Zariski dualizing complex whose `ε*` recovers the
chart restriction. -/
theorem normalizationDegree_comp_mapOfOver {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsLocallyNoetherian X] {ω : DerivedQCoh X} (hω : forallEtaleScheme ω) {U : Over S}
    (φ : ofOver U ⟶ X) [Etale φ] [AlgebraicGeometry.IsLocallyNoetherian U.left]
    (ωU : Scheme.DerivedQCoh U.left) (hωU : Scheme.IsDualizingComplex ωU.obj)
    (hiso : IsIsomorphic
      ((toEtaleDerived U).obj ((ModuleDerived.pullback φ).obj ((inclusion X).obj ω)))
      ((SmallEtale.inclusion U.left).obj ((epsilonStar U.left).obj ωU))) :
    normalizationDegree hω ∘ Points.mapOfOver φ =
      Scheme.IsDualizingComplex.normalizationDegree hωU :=
  sorry

/-- The canonical normalization-degree function of a dualizing complex on a locally Noetherian
quasi-separated algebraic space is a dimension function. -/
@[instance]
theorem normalizationDegree_isDimensionFunction {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsLocallyNoetherian X] [IsQuasiSeparated X] {ω : DerivedQCoh X}
    (hω : forallEtaleScheme ω) :
    IsDimensionFunction (normalizationDegree hω) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.DerivedQCoh
