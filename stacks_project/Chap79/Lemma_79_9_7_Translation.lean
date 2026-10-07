module

public import stacks_project.Chap78.Definition_78_11_1_Groupoid

/-!
# Left translation for groupoids in algebraic spaces

A source section of a groupoid in algebraic spaces determines left translation
on the arrow space by composition against that section.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidAlgebraicSpace

/-- A source section and the identity of the arrow space form a composable pair after
pullback along the target map. -/
theorem leftTranslationComposable {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) (a : G.U ⟶ G.R) (ha : a ≫ G.s = 𝟙 G.U) :
    (G.t ≫ a) ≫ G.s = (𝟙 G.R) ≫ G.t := sorry

/-- Left translation by a source section of a groupoid in algebraic spaces. -/
def leftTranslation {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) (a : G.U ⟶ G.R) (ha : a ≫ G.s = 𝟙 G.U) :
    G.R ⟶ G.R :=
  G.compose (G.t ≫ a) (𝟙 G.R) (leftTranslationComposable G a ha)

/-- Left translation is the pointwise composite with the chosen source section. -/
theorem leftTranslation_def {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) (a : G.U ⟶ G.R) (ha : a ≫ G.s = 𝟙 G.U) :
    G.leftTranslation a ha =
      G.compose (G.t ≫ a) (𝟙 G.R) (leftTranslationComposable G a ha) := sorry

/-- Left translation sends the identity section to the translating section. -/
theorem leftTranslation_identity {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) (a : G.U ⟶ G.R) (ha : a ≫ G.s = 𝟙 G.U) :
    G.e ≫ G.leftTranslation a ha = a := sorry

/-- Translation by a source section with invertible target map is an automorphism. -/
instance instIsIso_leftTranslation {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) (a : G.U ⟶ G.R) (ha : a ≫ G.s = 𝟙 G.U)
    [IsIso (a ≫ G.t)] : IsIso (G.leftTranslation a ha) := sorry

/-- The source section obtained by normalizing an arrow whose source map is an automorphism. -/
def sourceSection {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) (r : G.U ⟶ G.R) [IsIso (r ≫ G.s)] :
    G.U ⟶ G.R :=
  inv (r ≫ G.s) ≫ r

/-- The normalized arrow is a section of the source map. -/
theorem sourceSection_source {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) (r : G.U ⟶ G.R) [IsIso (r ≫ G.s)] :
    G.sourceSection r ≫ G.s = 𝟙 G.U := sorry

/-- Postcomposing with the source automorphism recovers `r` from `sourceSection r`. -/
theorem sourceSection_comp {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) (r : G.U ⟶ G.R) [IsIso (r ≫ G.s)] :
    (r ≫ G.s) ≫ G.sourceSection r = r := sorry

/-- Left translation by the source section associated to an arrow with invertible source. -/
def leftTranslationAt {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) (r : G.U ⟶ G.R) [IsIso (r ≫ G.s)] :
    G.R ⟶ G.R :=
  G.leftTranslation (G.sourceSection r) (G.sourceSection_source r)

/-- Translation at `r` is composition with its associated source section. -/
theorem leftTranslationAt_def {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) (r : G.U ⟶ G.R) [IsIso (r ≫ G.s)] :
    G.leftTranslationAt r =
      G.compose (G.t ≫ G.sourceSection r) (𝟙 G.R)
        (G.leftTranslationComposable (G.sourceSection r) (G.sourceSection_source r)) := sorry

/-- Left translation at an arrow with invertible source and target maps is an automorphism. -/
instance instIsIso_leftTranslationAt {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) (r : G.U ⟶ G.R)
    [IsIso (r ≫ G.s)] [IsIso (r ≫ G.t)] : IsIso (G.leftTranslationAt r) := sorry

/-- Left translation at `r` sends the identity section to the associated source section. -/
theorem leftTranslationAt_mapsIdentity {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) (r : G.U ⟶ G.R) [IsIso (r ≫ G.s)] :
    G.e ≫ G.leftTranslationAt r = G.sourceSection r := sorry

end AlgebraicGeometry.GroupoidAlgebraicSpace
