module

public import stacks_project.Chap65.Lemma_65_7_3_Pullback
public import stacks_project.Chap66.Definition_66_3_1_Separation
public import stacks_project.Chap66.Definition_66_5_1_QuasiCompact
public import stacks_project.Chap66.Lemma_66_16_5_Pullback
public import stacks_project.Chap66.Lemma_66_18_8_Pullback
public import stacks_project.Chap66.«66_27_0_1_Comparison»
public import stacks_project.Chap67.Definition_67_20_2_Affine
public import stacks_project.Chap75.Definition_75_9_1_Square

/-!
# Induction on qcqs objects of the spaces-étale site

A property of objects of `X_spaces,étale` that holds for affine objects and is
preserved by elementary distinguished squares, with the stated size conditions,
holds for every quasi-compact quasi-separated object of the site.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The structure morphism of the fibre product `U ×_W V` over `X` is étale when
`f.left` is étale. -/
theorem spacesEtaleSite.etale_fiber_hom {S : Scheme.{u}} {X : AlgebraicSpace S}
    {U V W : spacesEtaleSite X} (j : U ⟶ W) (f : V ⟶ W) [Etale f.left] :
    Etale (pullback.fst j.left f.left ≫ U.hom) :=
  sorry

/-- The fibre product `U ×_W V` as an object of `X_spaces,étale`, structured over `X`
by `pullback.fst j.left f.left ≫ U.hom`. -/
noncomputable abbrev spacesEtaleSite.fiber {S : Scheme.{u}} {X : AlgebraicSpace S}
    {U V W : spacesEtaleSite X} (j : U ⟶ W) (f : V ⟶ W) [Etale f.left] :
    spacesEtaleSite X :=
  MorphismProperty.Over.mk ⊤ (pullback.fst j.left f.left ≫ U.hom)
    (spacesEtaleSite.etale_fiber_hom j f)

/-- The underlying algebraic space of `spacesEtaleSite.fiber j f` is the fibre product
of `j.left` and `f.left`. -/
@[simp]
theorem spacesEtaleSite.fiber_left {S : Scheme.{u}} {X : AlgebraicSpace S}
    {U V W : spacesEtaleSite X} (j : U ⟶ W) (f : V ⟶ W) [Etale f.left] :
    (spacesEtaleSite.fiber j f).left = pullback j.left f.left :=
  sorry

/-- The structure morphism of `spacesEtaleSite.fiber j f` is
`pullback.fst j.left f.left ≫ U.hom`. -/
@[simp]
theorem spacesEtaleSite.fiber_hom {S : Scheme.{u}} {X : AlgebraicSpace S}
    {U V W : spacesEtaleSite X} (j : U ⟶ W) (f : V ⟶ W) [Etale f.left] :
    (spacesEtaleSite.fiber j f).hom = pullback.fst j.left f.left ≫ U.hom :=
  sorry

/-- A property of objects of `X_spaces,étale` that holds for every affine object and is
preserved by elementary distinguished squares `(j : U ⟶ W, f : V ⟶ W)` with `W`
quasi-compact and quasi-separated, `U` quasi-compact, `V` affine, and the property true
on `U`, `V`, and `U ×_W V`, holds for every quasi-compact quasi-separated object of the
site. -/
theorem qcqsSpacesEtale_induction {S : Scheme.{u}} (X : AlgebraicSpace S)
    [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X] (P : spacesEtaleSite X → Prop)
    (h_affine : ∀ (W : spacesEtaleSite X) [IsAffine W.left], P W)
    (h_square : ∀ {U V W : spacesEtaleSite X} (j : U ⟶ W) (f : V ⟶ W)
      [IsElementaryDistinguishedSquare j.left f.left] [h_etale : Etale f.left]
      [IsQuasiCompact W.left] [IsAbsolutelyQuasiSeparated W.left]
      [IsQuasiCompact U.left] [IsAffine V.left],
      P U → P V → P (spacesEtaleSite.fiber j f) → P W)
    (W : spacesEtaleSite X) [IsQuasiCompact W.left] [IsAbsolutelyQuasiSeparated W.left] :
    P W :=
  sorry

/-- In particular, such a property holds for the final object `spacesEtaleSite.self X`. -/
theorem qcqsSpacesEtale_induction_self {S : Scheme.{u}} (X : AlgebraicSpace S)
    [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X] (P : spacesEtaleSite X → Prop)
    (h_affine : ∀ (W : spacesEtaleSite X) [IsAffine W.left], P W)
    (h_square : ∀ {U V W : spacesEtaleSite X} (j : U ⟶ W) (f : V ⟶ W)
      [IsElementaryDistinguishedSquare j.left f.left] [h_etale : Etale f.left]
      [IsQuasiCompact W.left] [IsAbsolutelyQuasiSeparated W.left]
      [IsQuasiCompact U.left] [IsAffine V.left],
      P U → P V → P (spacesEtaleSite.fiber j f) → P W) :
    P (spacesEtaleSite.self X) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
