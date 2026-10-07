module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid

/-!
# Composition of source sections in a groupoid in algebraic spaces
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidAlgebraicSpace.SourceSection

variable {S : Scheme.{u}} [HasPullbacks (AlgebraicSpace S)]

/-- The later arrow `δ2 ≫ G.t ≫ δ1` and the earlier arrow `δ2` are composable
when `δ1` is a source section. -/
theorem composable {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) (δ1 δ2 : G.U ⟶ G.R)
    (hδ1 : δ1 ≫ G.s = 𝟙 G.U) :
    (δ2 ≫ G.t ≫ δ1) ≫ G.s = δ2 ≫ G.t := by
  simp [Category.assoc, hδ1]

/-- The composable pair `(δ2 ≫ G.t ≫ δ1, δ2)` as a morphism into `pullback G.s G.t`. -/
def pair {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B)
    (δ1 δ2 : G.U ⟶ G.R) (hδ1 : δ1 ≫ G.s = 𝟙 G.U) (hδ2 : δ2 ≫ G.s = 𝟙 G.U) :
    G.U ⟶ pullback G.s G.t :=
  pullback.lift (δ2 ≫ G.t ≫ δ1) δ2 (composable G δ1 δ2 hδ1)

/-- The first projection of the source-section pair is the later arrow `δ2 ≫ G.t ≫ δ1`. -/
theorem pair_fst {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) (δ1 δ2 : G.U ⟶ G.R)
    (hδ1 : δ1 ≫ G.s = 𝟙 G.U) (hδ2 : δ2 ≫ G.s = 𝟙 G.U) :
    pair G δ1 δ2 hδ1 hδ2 ≫ pullback.fst G.s G.t = δ2 ≫ G.t ≫ δ1 := sorry

/-- The second projection of the source-section pair is the earlier arrow `δ2`. -/
theorem pair_snd {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) (δ1 δ2 : G.U ⟶ G.R)
    (hδ1 : δ1 ≫ G.s = 𝟙 G.U) (hδ2 : δ2 ≫ G.s = 𝟙 G.U) :
    pair G δ1 δ2 hδ1 hδ2 ≫ pullback.snd G.s G.t = δ2 := sorry

/-- Composition of two source sections as a morphism `G.U ⟶ G.R`. -/
def comp {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B)
    (δ1 δ2 : G.U ⟶ G.R) (hδ1 : δ1 ≫ G.s = 𝟙 G.U) (hδ2 : δ2 ≫ G.s = 𝟙 G.U) :
    G.U ⟶ G.R :=
  G.compose (δ2 ≫ G.t ≫ δ1) δ2 (composable G δ1 δ2 hδ1)

/-- The composite of two source sections is again a source section. -/
theorem comp_source {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) (δ1 δ2 : G.U ⟶ G.R)
    (hδ1 : δ1 ≫ G.s = 𝟙 G.U) (hδ2 : δ2 ≫ G.s = 𝟙 G.U) :
    comp G δ1 δ2 hδ1 hδ2 ≫ G.s = 𝟙 G.U := sorry

/-- The composition of source sections is the ambient groupoid composition of the induced pair. -/
theorem comp_eq {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) (δ1 δ2 : G.U ⟶ G.R)
    (hδ1 : δ1 ≫ G.s = 𝟙 G.U) (hδ2 : δ2 ≫ G.s = 𝟙 G.U) :
    comp G δ1 δ2 hδ1 hδ2 =
      G.compose (δ2 ≫ G.t ≫ δ1) δ2 (composable G δ1 δ2 hδ1) := sorry

end AlgebraicGeometry.GroupoidAlgebraicSpace.SourceSection
