module

public import stacks_project.Chap79.Lemma_79_12_14
public import stacks_project.Chap79.Lemma_79_14_1_Groupoid
public import stacks_project.Chap79.Lemma_79_14_1_Section
public import stacks_project.Chap79.Lemma_79_15_5_Existence_of_strong_splitting_OfScheme

/-!
# Scheme and separated finite-part localizations

If `f` is separated, flat, and locally of finite presentation, then the
finite-part-with-section space `(X / Y, σ)_fin` is a scheme whenever `Y` is,
and its structure morphism to `Y` is separated. Specializing to the source of
a groupoid scheme yields the same conclusions for the finite-part object space
and `finitePartToU`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace

universe u

noncomputable section

namespace AlgebraicGeometry.AlgebraicSpace.FinitePart

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S}

/-- The finite-part-with-section space `(X / Y, σ)_fin` is a scheme when `f` is
separated, flat, and locally of finite presentation and `Y` is a scheme. -/
instance instIsScheme_withSectionSpace (f : X ⟶ Y) [Separated f]
    [LocallyOfFiniteType f] [Flat f] [LocallyOfFinitePresentation f] [IsScheme Y]
    (σ : Y ⟶ X) (hσ : σ ≫ f = 𝟙 Y) : IsScheme (withSectionSpace f σ hσ) :=
  sorry

/-- The structure morphism `(X / Y, σ)_fin ⟶ Y` is separated when `f` is
separated, flat, and locally of finite presentation. -/
instance instSeparated_withSectionToY (f : X ⟶ Y) [Separated f]
    [LocallyOfFiniteType f] [Flat f] [LocallyOfFinitePresentation f]
    (σ : Y ⟶ X) (hσ : σ ≫ f = 𝟙 Y) : Separated (withSectionToY f σ hσ) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.FinitePart

namespace AlgebraicGeometry.GroupoidAlgebraicSpace

/-- Flatness of the source of a groupoid scheme transfers to `ofScheme`. -/
instance ofScheme_source_flat {S : Scheme.{u}} (G : GroupoidScheme S)
    [AlgebraicGeometry.Flat G.s.left] : AlgebraicSpace.Flat (ofScheme G).s.left :=
  (flat_ofOverMap_iff G.s).mpr inferInstance

/-- Flatness of the target of a groupoid scheme transfers to `ofScheme`. -/
instance ofScheme_target_flat {S : Scheme.{u}} (G : GroupoidScheme S)
    [AlgebraicGeometry.Flat G.t.left] : AlgebraicSpace.Flat (ofScheme G).t.left :=
  (flat_ofOverMap_iff G.t).mpr inferInstance

/-- Local finite presentation of the source of a groupoid scheme transfers to
`ofScheme`. -/
instance ofScheme_source_locallyOfFinitePresentation {S : Scheme.{u}}
    (G : GroupoidScheme S)
    [AlgebraicGeometry.LocallyOfFinitePresentation G.s.left] :
    AlgebraicSpace.LocallyOfFinitePresentation (ofScheme G).s.left :=
  sorry

/-- Local finite presentation of the target of a groupoid scheme transfers to
`ofScheme`. -/
instance ofScheme_target_locallyOfFinitePresentation {S : Scheme.{u}}
    (G : GroupoidScheme S)
    [AlgebraicGeometry.LocallyOfFinitePresentation G.t.left] :
    AlgebraicSpace.LocallyOfFinitePresentation (ofScheme G).t.left :=
  sorry

/-- The finite-part object space of a groupoid scheme is a scheme when the
source is separated, locally of finite type, flat, and locally of finite
presentation. -/
instance instIsScheme_finitePart_U {S : Scheme.{u}} (G : GroupoidScheme S)
    [AlgebraicSpace.Separated (ofScheme G).s.left]
    [AlgebraicSpace.LocallyOfFiniteType (ofScheme G).s.left]
    [AlgebraicSpace.Separated (ofScheme G).t.left]
    [AlgebraicSpace.LocallyOfFiniteType (ofScheme G).t.left]
    [AlgebraicSpace.Flat (ofScheme G).s.left]
    [AlgebraicSpace.LocallyOfFinitePresentation (ofScheme G).s.left] :
    AlgebraicSpace.IsScheme (finitePart (ofScheme G)).U.left :=
  sorry

/-- The finite-part morphism `U' ⟶ U` of a groupoid scheme is separated when
the source is separated, locally of finite type, flat, and locally of finite
presentation. -/
instance instSeparated_finitePartToU {S : Scheme.{u}} (G : GroupoidScheme S)
    [AlgebraicSpace.Separated (ofScheme G).s.left]
    [AlgebraicSpace.LocallyOfFiniteType (ofScheme G).s.left]
    [AlgebraicSpace.Separated (ofScheme G).t.left]
    [AlgebraicSpace.LocallyOfFiniteType (ofScheme G).t.left]
    [AlgebraicSpace.Flat (ofScheme G).s.left]
    [AlgebraicSpace.LocallyOfFinitePresentation (ofScheme G).s.left] :
    AlgebraicSpace.Separated (finitePartToU (ofScheme G)) :=
  sorry

end AlgebraicGeometry.GroupoidAlgebraicSpace
