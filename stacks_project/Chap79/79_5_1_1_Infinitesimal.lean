module

public import stacks_project.Chap65.Lemma_65_7_3_Pullback
public import stacks_project.Chap65.Lemma_65_12_4_Immersion
public import stacks_project.Chap76.Lemma_76_9_8_Pullback
public import stacks_project.Chap79.«79_5_1_1_Section»

/-!
# Infinitesimal source sections of a groupoid in algebraic spaces

Given a first-order thickening `ι : U₀ ⟶ U` of the object space of a groupoid
in algebraic spaces, the restricted arrow space is `R₀ = s⁻¹(U₀)`, the
restricted identity is `e₀`, and an infinitesimal section is a source section
`δ` with `δ|_{U₀} = e₀`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidAlgebraicSpace

variable {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B)
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

/-- The composite `e₀ ≫ (R₀ ⊂ R)` is `ι ≫ e`. -/
theorem identityRestrict_comp_arrowι :
    identityRestrict G ι ≫ arrowι G ι = ι ≫ G.e.left := sorry

/-- The commutative square of the identity section over the first-order thickening. -/
theorem identityCommSq :
    CommSq (identityRestrict G ι) ι (arrowι G ι) G.e.left := sorry

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

end AlgebraicGeometry.GroupoidAlgebraicSpace
