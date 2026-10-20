module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.SourceSection
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Thickening.FirstOrder
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Deformation.Difference
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Differentials.Pullback
public import ReasLib.CategoryTheory.Subobject.Invariant

/-!
# Infinitesimal source sections and differential parameters

Source sections restricting to the identity along a first-order thickening are
related to linear maps from pulled-back relative differentials to the conormal sheaf.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits
open AlgebraicGeometry.AlgebraicSpace hiding Hom

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidAlgebraicSpace

variable {S : Scheme.{u}} [HasPullbacks (AlgebraicSpace S)] {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B)
variable {U₀ : AlgebraicSpace S} (ι : U₀ ⟶ G.U.left)

/-- The restricted arrow space `R₀ = s⁻¹(U₀)`, as the pullback of `s` along `ι`. -/
def arrowRestrict : AlgebraicSpace S :=
  pullback ι G.s.left

/-- The restricted source map `s₀ : R₀ ⟶ U₀`. -/
def sourceRestrict : arrowRestrict G ι ⟶ U₀ :=
  pullback.fst ι G.s.left

/-- The closed immersion `R₀ ⊂ R`. -/
def arrowι : arrowRestrict G ι ⟶ G.R.left :=
  pullback.snd ι G.s.left

/-- The two legs of `R₀` agree over `U`. -/
theorem arrowRestrict_condition :
    sourceRestrict G ι ≫ ι = arrowι G ι ≫ G.s.left := sorry

/-- The identity section and `ι` agree over `U` after composing with `s`. -/
theorem identityRestrict_condition :
    𝟙 U₀ ≫ ι = (ι ≫ G.e.left) ≫ G.s.left := sorry

/-- The restricted identity `e₀ : U₀ ⟶ R₀`. -/
def identityRestrict : U₀ ⟶ arrowRestrict G ι :=
  pullback.lift (𝟙 U₀) (ι ≫ G.e.left) (identityRestrict_condition G ι)

/-- The first projection of `e₀` is the identity on `U₀`. -/
theorem identityRestrict_fst :
    identityRestrict G ι ≫ sourceRestrict G ι = 𝟙 U₀ := sorry

/-- The second projection of `e₀` is `ι ≫ e`. -/
theorem identityRestrict_snd :
    identityRestrict G ι ≫ arrowι G ι = ι ≫ G.e.left := sorry

/-- The commutative square of the identity section over the first-order thickening. -/
theorem identityCommSq :
    CommSq (identityRestrict G ι) ι (arrowι G ι) G.e.left :=
  ⟨identityRestrict_snd G ι⟩

/-- An infinitesimal source section: a source section of `G` whose restriction
to `U₀` is the restricted identity `e₀`. -/
structure InfinitesimalSection [AlgebraicSpace.IsFirstOrderThickening ι] where
  /-- The underlying morphism `U ⟶ R`. -/
  arrow : G.U ⟶ G.R
  /-- The source of the section is the identity on objects. -/
  source : arrow ≫ G.s = 𝟙 G.U
  /-- The restriction to `U₀` is `e₀`. -/
  restrict : identityRestrict G ι ≫ arrowι G ι = ι ≫ arrow.left

/-- Build an infinitesimal section from an arrow with the source and restriction
conditions. -/
def InfinitesimalSection.of [AlgebraicSpace.IsFirstOrderThickening ι]
    (arrow : G.U ⟶ G.R) (source : arrow ≫ G.s = 𝟙 G.U)
    (restrict : identityRestrict G ι ≫ arrowι G ι = ι ≫ arrow.left) :
    InfinitesimalSection G ι :=
  ⟨arrow, source, restrict⟩

/-- Forget an infinitesimal section to its underlying source section. -/
def InfinitesimalSection.toSection [AlgebraicSpace.IsFirstOrderThickening ι]
    (δ : InfinitesimalSection G ι) : Section G :=
  Section.of G δ.arrow δ.source

/-- The underlying arrow of `toSection` is the infinitesimal section's arrow. -/
theorem InfinitesimalSection.toSection_arrow [AlgebraicSpace.IsFirstOrderThickening ι]
    (δ : InfinitesimalSection G ι) :
    (InfinitesimalSection.toSection G ι δ).arrow = δ.arrow := rfl

/-- The identity section is infinitesimal. -/
def InfinitesimalSection.id [AlgebraicSpace.IsFirstOrderThickening ι] :
    InfinitesimalSection G ι :=
  InfinitesimalSection.of G ι G.e G.identity_source (identityRestrict_snd G ι)

/-- The underlying arrow of the infinitesimal identity is `e`. -/
theorem InfinitesimalSection.id_arrow [AlgebraicSpace.IsFirstOrderThickening ι] :
    (InfinitesimalSection.id G ι).arrow = G.e := rfl

/-- A differential parameter is a linear map from the restricted identity's
pullback of relative differentials to the conormal sheaf of the thickening. -/
abbrev Parameter [IsFirstOrderThickening ι] :=
  (Modules.pullback (identityRestrict G ι)).obj
      (AlgebraicSpace.Hom.relativeDifferentials (sourceRestrict G ι)) ⟶
    AlgebraicSpace.Hom.conormalSheaf ι

/-- Differential parameters are exactly the indicated differential-to-conormal module maps. -/
theorem Parameter_eq [IsFirstOrderThickening ι] :
    Parameter G ι =
      ((Modules.pullback (identityRestrict G ι)).obj
          (AlgebraicSpace.Hom.relativeDifferentials (sourceRestrict G ι)) ⟶
        AlgebraicSpace.Hom.conormalSheaf ι) := rfl

/-- An infinitesimal source section is the perturbation by a parameter when its
structure map minus the identity's structure map is the induced derivation
followed by the first-order conormal inclusion. -/
def IsPerturbation [IsFirstOrderThickening ι] (θ : Parameter G ι)
    (δ : InfinitesimalSection G ι) : Prop :=
  AlgebraicSpace.Hom.Deformation.structureMapDifference_restrict
      ι (arrowι G ι) (identityRestrict G ι) δ.arrow.left G.e.left
      δ.restrict.symm (identityCommSq G ι).w.symm =
    AlgebraicSpace.Hom.Deformation.factorizationMap
      (sourceRestrict G ι) ι (arrowι G ι) (identityRestrict G ι)
      (AlgebraicSpace.Hom.derivationOfPullback
        (sourceRestrict G ι) (identityRestrict G ι) θ)

/-- The perturbation relation is the equality of the ordered structure-map
difference with the conormal factorization of the parameter's derivation. -/
theorem isPerturbation_iff [IsFirstOrderThickening ι] (θ : Parameter G ι)
    (δ : InfinitesimalSection G ι) :
    IsPerturbation G ι θ δ ↔
      AlgebraicSpace.Hom.Deformation.structureMapDifference_restrict
          ι (arrowι G ι) (identityRestrict G ι) δ.arrow.left G.e.left
          δ.restrict.symm (identityCommSq G ι).w.symm =
        AlgebraicSpace.Hom.Deformation.factorizationMap
          (sourceRestrict G ι) ι (arrowι G ι) (identityRestrict G ι)
          (AlgebraicSpace.Hom.derivationOfPullback
            (sourceRestrict G ι) (identityRestrict G ι) θ) := Iff.rfl

/-- Each differential parameter determines a unique infinitesimal source section
whose ordered structure-map difference is its conormal-valued derivation. -/
theorem existsUnique_infinitesimalSection_of_parameter
    [IsFirstOrderThickening ι] (θ : Parameter G ι) :
    ∃! δ : InfinitesimalSection G ι, IsPerturbation G ι θ δ := sorry

/-- Along an invariant first-order thickening, the perturbation relation gives
unique infinitesimal source sections for parameters and unique parameters for sections. -/
theorem isPerturbation_bijective [IsFirstOrderThickening ι]
    (h_invariant : CategoryTheory.Subobject.IsInvariant G.s.left G.t.left (Subobject.mk ι)) :
    (∀ θ : Parameter G ι, ∃! δ : InfinitesimalSection G ι, IsPerturbation G ι θ δ) ∧
      (∀ δ : InfinitesimalSection G ι, ∃! θ : Parameter G ι, IsPerturbation G ι θ δ) := by
  refine ⟨existsUnique_infinitesimalSection_of_parameter G ι, ?_⟩
  sorry

end AlgebraicGeometry.GroupoidAlgebraicSpace
