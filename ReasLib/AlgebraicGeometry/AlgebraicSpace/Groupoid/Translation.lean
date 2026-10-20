module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Pullback

/-!
# Left translation for groupoids in algebraic spaces

A source section determines left translation on the arrow space. An arrow with
invertible source composite determines such a section by source normalization.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidAlgebraicSpace

/-- Left translation by a source section of a groupoid in algebraic spaces. -/
def leftTranslation {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) (a : G.U ⟶ G.R) (ha : a ≫ G.s = 𝟙 G.U) :
    G.R ⟶ G.R :=
  G.compose (G.t ≫ a) (𝟙 G.R) (by
    rw [Category.assoc, ha, Category.comp_id, Category.id_comp])

/-- Left translation is the pointwise composite with the chosen source section. -/
theorem leftTranslation_def {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) (a : G.U ⟶ G.R) (ha : a ≫ G.s = 𝟙 G.U) :
    G.leftTranslation a ha =
      G.compose (G.t ≫ a) (𝟙 G.R) (by
        rw [Category.assoc, ha, Category.comp_id, Category.id_comp]) := rfl

/-- Left translation sends the identity section to the translating section. -/
theorem leftTranslation_identity {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) (a : G.U ⟶ G.R) (ha : a ≫ G.s = 𝟙 G.U) :
    G.e ≫ G.leftTranslation a ha = a := sorry

/-- Translation by a source section with invertible target composite is an automorphism. -/
theorem isIso_leftTranslation {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) (a : G.U ⟶ G.R) (ha : a ≫ G.s = 𝟙 G.U)
    [IsIso (a ≫ G.t)] : IsIso (G.leftTranslation a ha) := sorry

/-- An arrow with invertible source composite gives a source section by precomposition
with the inverse source automorphism. -/
def sourceSection {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) (r : G.U.left ⟶ G.R.left)
    [IsIso (r ≫ G.s.left)] : G.U ⟶ G.R :=
  Over.homMk (inv (r ≫ G.s.left) ≫ r) (by
    calc
      (inv (r ≫ G.s.left) ≫ r) ≫ G.R.hom =
          inv (r ≫ G.s.left) ≫ (r ≫ G.s.left) ≫ G.U.hom := by
            rw [Category.assoc, ← Over.w G.s]
            simp only [Category.assoc]
      _ = G.U.hom := by rw [IsIso.inv_hom_id_assoc])

/-- The normalized arrow is a section of the source map. -/
theorem sourceSection_source {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) (r : G.U.left ⟶ G.R.left)
    [IsIso (r ≫ G.s.left)] :
    G.sourceSection r ≫ G.s = 𝟙 G.U := sorry

/-- Precomposition with the source automorphism recovers the original arrow
from its normalized source section. -/
theorem sourceSection_comp {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) (r : G.U.left ⟶ G.R.left)
    [IsIso (r ≫ G.s.left)] :
    (r ≫ G.s.left) ≫ (G.sourceSection r).left = r := sorry

/-- Left translation by the normalized source section of an arrow with invertible source. -/
def leftTranslationAt {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) (r : G.U.left ⟶ G.R.left)
    [IsIso (r ≫ G.s.left)] : G.R ⟶ G.R :=
  G.leftTranslation (G.sourceSection r) (G.sourceSection_source r)

/-- Translation at an arrow is composition with its normalized source section. -/
theorem leftTranslationAt_def {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) (r : G.U.left ⟶ G.R.left)
    [IsIso (r ≫ G.s.left)] :
    G.leftTranslationAt r =
      G.compose (G.t ≫ G.sourceSection r) (𝟙 G.R) (by
        rw [Category.assoc, G.sourceSection_source r, Category.comp_id,
          Category.id_comp]) := rfl

/-- Left translation at an arrow with invertible source and target composites
is an automorphism of the arrow space. -/
theorem isIso_leftTranslationAt {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) (r : G.U.left ⟶ G.R.left)
    [IsIso (r ≫ G.s.left)] [IsIso (r ≫ G.t.left)] :
    IsIso (G.leftTranslationAt r) := sorry

/-- Left translation at an arrow sends the identity section to its normalized
source section. -/
theorem leftTranslationAt_mapsIdentity {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) (r : G.U.left ⟶ G.R.left)
    [IsIso (r ≫ G.s.left)] :
    G.e ≫ G.leftTranslationAt r = G.sourceSection r := sorry

/-- Translating the identity section and precomposing with the source automorphism
recovers the original arrow. -/
theorem leftTranslationAt_recoversArrow {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) (r : G.U.left ⟶ G.R.left)
    [IsIso (r ≫ G.s.left)] :
    (r ≫ G.s.left) ≫ G.e.left ≫ (G.leftTranslationAt r).left = r := sorry

end AlgebraicGeometry.GroupoidAlgebraicSpace
