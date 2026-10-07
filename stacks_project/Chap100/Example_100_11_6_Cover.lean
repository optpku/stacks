module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.Topology.JacobsonSpace
public import ReasLib.AlgebraicGeometry.ConstantGroup
public import stacks_project.Chap65.Example_65_14_7_ArtinSchreier
public import stacks_project.Chap65.Lemma_65_14_3_Relation
public import stacks_project.Chap65.Lemma_65_14_6_Equivariant

/-!
# Galois pullback cover over `Spec algebraicQ`

This module records the scheme
`U = Spec algebraicQ ×_{Spec ℚ} Spec algebraicQ` over `Spec algebraicQ`, the
diagonal section, the discrete Galois action on the first factor, and the
constant group scheme of `Gal(algebraicQ / ℚ)`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits
open AlgebraicGeometry.AlgebraicSpace.AlgebraicClosureQuotient
open AlgebraicGeometry.Scheme.PreRelation

noncomputable section

namespace AlgebraicGeometry.AlgebraicSpace.GaloisPullback

/-- The base scheme `S = Spec algebraicQ`. -/
abbrev base : Scheme.{0} := Spec (CommRingCat.of algebraicQ)

/-- The base scheme is the spectrum of `algebraicQ`. -/
theorem base_eq : base = Spec (CommRingCat.of algebraicQ) := sorry

/-- The structure morphism `Spec algebraicQ ⟶ Spec ℚ`. -/
abbrev specMapQ : Spec (CommRingCat.of algebraicQ) ⟶ Spec (CommRingCat.of ℚ) :=
  FieldExtension.specMap ℚ algebraicQ

/-- `specMapQ` is the canonical morphism induced by `ℚ ⟶ algebraicQ`. -/
theorem specMapQ_eq : specMapQ = FieldExtension.specMap ℚ algebraicQ := sorry

/-- The cover `U = Spec algebraicQ ×_{Spec ℚ} Spec algebraicQ` as a scheme over
`Spec algebraicQ`, via the second projection. -/
def cover : Over base :=
  Over.mk (pullback.snd specMapQ specMapQ)

/-- The underlying scheme of the cover is the fibre product of two copies of
`Spec algebraicQ` over `Spec ℚ`. -/
theorem cover_left :
    cover.left = pullback specMapQ specMapQ := sorry

/-- The structure morphism of the cover is the second projection of the fibre
product. -/
theorem cover_hom : cover.hom = pullback.snd specMapQ specMapQ := sorry

/-- The two legs of the diagonal section of `U` agree over `Spec ℚ`. -/
theorem sectionHom_condition : 𝟙 base ≫ specMapQ = 𝟙 base ≫ specMapQ := sorry

/-- The diagonal section `Spec algebraicQ ⟶ U` as a morphism of schemes. -/
def sectionLeft : base ⟶ cover.left :=
  pullback.lift (𝟙 base) (𝟙 base) rfl

/-- `sectionLeft` is the pullback lift of the pair of identities. -/
theorem sectionLeft_eq :
    sectionLeft = pullback.lift (𝟙 base) (𝟙 base) rfl := sorry

/-- The diagonal section lies over `Spec algebraicQ`. -/
theorem sectionHom_w : sectionLeft ≫ cover.hom = 𝟙 base := sorry

/-- The diagonal section `Spec algebraicQ ⟶ U` as a morphism over
`Spec algebraicQ`. -/
def sectionHom : Over.mk (𝟙 base) ⟶ cover :=
  Over.homMk sectionLeft sectionHom_w

/-- The underlying scheme morphism of `sectionHom` is `sectionLeft`. -/
theorem sectionHom_left : sectionHom.left = sectionLeft := sorry

/-- First-factor Galois action on `U` commutes with the left projection to
`Spec ℚ`. -/
theorem actionLeft_eq₁ (σ : gal) :
    specMapQ ≫ 𝟙 (Spec (CommRingCat.of ℚ)) = (galSpecAut σ).hom ≫ specMapQ :=
  sorry

/-- The identity on the second factor of `U` commutes with the projection to
`Spec ℚ`. -/
theorem actionLeft_eq₂ (σ : gal) :
    specMapQ ≫ 𝟙 (Spec (CommRingCat.of ℚ)) = 𝟙 base ≫ specMapQ := sorry

/-- The underlying scheme morphism of the Galois action of `σ` on `U`. -/
def actionLeft (σ : gal) : cover.left ⟶ cover.left :=
  pullback.map specMapQ specMapQ specMapQ specMapQ
    (galSpecAut σ).hom (𝟙 base) (𝟙 (Spec (CommRingCat.of ℚ)))
    (actionLeft_eq₁ σ) rfl

/-- `actionLeft σ` is `pullback.map` of `galSpecAut σ` on the first factor and
the identity on the second factor. -/
theorem actionLeft_eq (σ : gal) :
    actionLeft σ =
      pullback.map specMapQ specMapQ specMapQ specMapQ
        (galSpecAut σ).hom (𝟙 base) (𝟙 (Spec (CommRingCat.of ℚ)))
        (actionLeft_eq₁ σ) rfl := sorry

/-- The Galois action on `U` lies over `Spec algebraicQ`. -/
theorem actionLeft_w (σ : gal) : actionLeft σ ≫ cover.hom = cover.hom := sorry

/-- The Galois action of `σ` as an automorphism of the scheme `U`. -/
def actionIso (σ : gal) : cover.left ≅ cover.left where
  hom := actionLeft σ
  inv := actionLeft σ⁻¹
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The forward map of `actionIso σ` is `actionLeft σ`. -/
theorem actionIso_hom (σ : gal) : (actionIso σ).hom = actionLeft σ := sorry

/-- The inverse map of `actionIso σ` is `actionLeft σ⁻¹`. -/
theorem actionIso_inv (σ : gal) : (actionIso σ).inv = actionLeft σ⁻¹ := sorry

/-- The obvious action of `Gal(algebraicQ / ℚ)` on `U` over `Spec algebraicQ`,
acting on the first factor by `galSpecAut`. -/
def action : gal →* Aut cover where
  toFun σ := Over.isoMk (actionIso σ) (actionLeft_w σ)
  map_one' := sorry
  map_mul' := sorry

/-- The underlying scheme morphism of `action σ` is `actionLeft σ`. -/
theorem action_hom (σ : gal) : (action σ).hom.left = actionLeft σ := sorry

/-- The identity Galois element acts by the identity automorphism of the cover. -/
theorem action_one : action 1 = 1 := sorry

/-- Property `(*)` of Lemma 65.14.3: the Galois action on `U` is residue-field
free. -/
instance instIsResidueFieldFree_action : IsResidueFieldFree action := sorry

/-- The Galois action on `U` is transitive on topological points. -/
theorem exists_action_eq (u v : cover.left) :
    ∃ σ : gal, (action σ).hom.left u = v := sorry

/-- Every point of `U` is closed. -/
theorem mem_closedPoints_cover (u : cover.left) : u ∈ closedPoints cover.left :=
  sorry

/-- The absolute Galois group with the discrete topology, viewed as a constant
group scheme over `Spec algebraicQ`, as in Groupoids, Example 39.5.6. -/
def constantGroup : Grp (Over base) :=
  ConstantGroup.baseChange base (GrpCat.of gal)

/-- `constantGroup` is the base change of the constant group scheme on `gal`. -/
theorem constantGroup_eq :
    constantGroup = ConstantGroup.baseChange base (GrpCat.of gal) := sorry

/-- The spectrum of `algebraicQ` is reduced. -/
instance instIsReduced_base : AlgebraicGeometry.IsReduced base := inferInstance

/-- The spectrum of `algebraicQ` is locally Noetherian. -/
instance instIsLocallyNoetherian_base :
    AlgebraicGeometry.IsLocallyNoetherian base := inferInstance

end AlgebraicGeometry.AlgebraicSpace.GaloisPullback
