module

public import Mathlib.Data.List.TFAE
public import ReasLib.CategoryTheory.Fibered.Inertia.Groupoids.RelativeFunctoriality.Stable.Construction
public import stacks_project.Chap65.Lemma_65_12_4_Immersion
public import stacks_project.Chap101.Definition_101_4_1_Separation
import Mathlib.Tactic.CrossRefAttribute

/-!
# Relative inertia versus the first diagonal

For a morphism of algebraic stacks, scheme-slice separation, quasi-separation,
and local separation of `I_{X/Y} ⟶ X` are equivalent to the same properties of
the first diagonal `Hom.diagonal f`, and to the identity section
`identitySection f : X ⟶ I_{X/Y}` being a closed immersion, quasi-compact, or
an immersion, respectively. Unramifiedness (resp. local quasi-finiteness) of
`I_{X/Y} ⟶ X` is equivalent to `f` being DM (resp. quasi-DM).
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open FiberedCategoryOver.Groupoids
open FiberedCategoryOver.Groupoids.RelativeInertia
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack.RelativeInertia

/-- Lemma 101.6.1 (1): Let `f : X ⟶ Y` be a morphism of algebraic stacks. The
following are equivalent: `I_{X/Y} ⟶ X` is separated, the first diagonal
`Δ_{f,1} = Δ_f = Hom.diagonal f` is separated, and
`Δ_{f,2} = e = identitySection f : X ⟶ I_{X/Y}` is a closed immersion. -/
@[stacks 0CL0]
theorem forget_separated_tfae {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) :
    List.TFAE
      [Groupoids.Hom.has (@AlgebraicSpace.Separated S)
          (forget.{u + 1, u, u, u + 1} f),
        Groupoids.Hom.has (@AlgebraicSpace.Separated S)
          (Hom.diagonal.{u + 1, u, u + 1} f),
        Groupoids.Hom.has (@AlgebraicSpace.IsClosedImmersion S)
          (identitySection.{u + 1, u, u, u + 1} f)] :=
  sorry

/-- The relative-inertia forgetful morphism is separated on scheme-slice tests
if and only if the first diagonal is separated. -/
theorem forget_separated_iff_firstDiagonal_separated {S : Scheme.{u}}
    {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
    (f : X ⟶ Y) :
    Groupoids.Hom.has (@AlgebraicSpace.Separated S)
        (forget.{u + 1, u, u, u + 1} f) ↔
      Groupoids.Hom.has (@AlgebraicSpace.Separated S)
        (Hom.diagonal.{u + 1, u, u + 1} f) :=
  sorry

/-- The relative-inertia forgetful morphism is separated on scheme-slice tests
if and only if the identity section is a closed immersion. -/
theorem forget_separated_iff_identitySection_isClosedImmersion
    {S : Scheme.{u}} {X Y : GroupoidsOver S} [AlgebraicStack X]
    [AlgebraicStack Y] (f : X ⟶ Y) :
    Groupoids.Hom.has (@AlgebraicSpace.Separated S)
        (forget.{u + 1, u, u, u + 1} f) ↔
      Groupoids.Hom.has (@AlgebraicSpace.IsClosedImmersion S)
        (identitySection.{u + 1, u, u, u + 1} f) :=
  sorry

/-- The first diagonal of a morphism of algebraic stacks is separated on
scheme-slice tests if and only if the identity section is a closed
immersion. -/
theorem firstDiagonal_separated_iff_identitySection_isClosedImmersion
    {S : Scheme.{u}} {X Y : GroupoidsOver S} [AlgebraicStack X]
    [AlgebraicStack Y] (f : X ⟶ Y) :
    Groupoids.Hom.has (@AlgebraicSpace.Separated S)
        (Hom.diagonal.{u + 1, u, u + 1} f) ↔
      Groupoids.Hom.has (@AlgebraicSpace.IsClosedImmersion S)
        (identitySection.{u + 1, u, u, u + 1} f) :=
  sorry

/-- Lemma 101.6.1 (2): Let `f : X ⟶ Y` be a morphism of algebraic stacks. The
following are equivalent: `I_{X/Y} ⟶ X` is quasi-separated, the first diagonal
`Δ_{f,1} = Δ_f = Hom.diagonal f` is quasi-separated, and
`Δ_{f,2} = e = identitySection f : X ⟶ I_{X/Y}` is quasi-compact. -/
@[stacks 0CL0]
theorem forget_quasiSeparated_tfae {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) :
    List.TFAE
      [Groupoids.Hom.has (@AlgebraicSpace.QuasiSeparated S)
          (forget.{u + 1, u, u, u + 1} f),
        Groupoids.Hom.has (@AlgebraicSpace.QuasiSeparated S)
          (Hom.diagonal.{u + 1, u, u + 1} f),
        Groupoids.Hom.has (@AlgebraicSpace.QuasiCompact S)
          (identitySection.{u + 1, u, u, u + 1} f)] :=
  sorry

/-- The relative-inertia forgetful morphism is quasi-separated on scheme-slice
tests if and only if the first diagonal is quasi-separated. -/
theorem forget_quasiSeparated_iff_firstDiagonal_quasiSeparated
    {S : Scheme.{u}} {X Y : GroupoidsOver S} [AlgebraicStack X]
    [AlgebraicStack Y] (f : X ⟶ Y) :
    Groupoids.Hom.has (@AlgebraicSpace.QuasiSeparated S)
        (forget.{u + 1, u, u, u + 1} f) ↔
      Groupoids.Hom.has (@AlgebraicSpace.QuasiSeparated S)
        (Hom.diagonal.{u + 1, u, u + 1} f) :=
  sorry

/-- The relative-inertia forgetful morphism is quasi-separated on scheme-slice
tests if and only if the identity section is quasi-compact. -/
theorem forget_quasiSeparated_iff_identitySection_quasiCompact
    {S : Scheme.{u}} {X Y : GroupoidsOver S} [AlgebraicStack X]
    [AlgebraicStack Y] (f : X ⟶ Y) :
    Groupoids.Hom.has (@AlgebraicSpace.QuasiSeparated S)
        (forget.{u + 1, u, u, u + 1} f) ↔
      Groupoids.Hom.has (@AlgebraicSpace.QuasiCompact S)
        (identitySection.{u + 1, u, u, u + 1} f) :=
  sorry

/-- The first diagonal of a morphism of algebraic stacks is quasi-separated on
scheme-slice tests if and only if the identity section is quasi-compact. -/
theorem firstDiagonal_quasiSeparated_iff_identitySection_quasiCompact
    {S : Scheme.{u}} {X Y : GroupoidsOver S} [AlgebraicStack X]
    [AlgebraicStack Y] (f : X ⟶ Y) :
    Groupoids.Hom.has (@AlgebraicSpace.QuasiSeparated S)
        (Hom.diagonal.{u + 1, u, u + 1} f) ↔
      Groupoids.Hom.has (@AlgebraicSpace.QuasiCompact S)
        (identitySection.{u + 1, u, u, u + 1} f) :=
  sorry

/-- Lemma 101.6.1 (3): Let `f : X ⟶ Y` be a morphism of algebraic stacks. The
following are equivalent: `I_{X/Y} ⟶ X` is locally separated, the first
diagonal `Δ_{f,1} = Δ_f = Hom.diagonal f` is locally separated, and
`Δ_{f,2} = e = identitySection f : X ⟶ I_{X/Y}` is an immersion. -/
@[stacks 0CL0]
theorem forget_locallySeparated_tfae {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) :
    List.TFAE
      [Groupoids.Hom.has (@AlgebraicSpace.LocallySeparated S)
          (forget.{u + 1, u, u, u + 1} f),
        Groupoids.Hom.has (@AlgebraicSpace.LocallySeparated S)
          (Hom.diagonal.{u + 1, u, u + 1} f),
        Groupoids.Hom.has (@AlgebraicSpace.IsImmersion S)
          (identitySection.{u + 1, u, u, u + 1} f)] :=
  sorry

/-- The relative-inertia forgetful morphism is locally separated on scheme-slice
tests if and only if the first diagonal is locally separated. -/
theorem forget_locallySeparated_iff_firstDiagonal_locallySeparated
    {S : Scheme.{u}} {X Y : GroupoidsOver S} [AlgebraicStack X]
    [AlgebraicStack Y] (f : X ⟶ Y) :
    Groupoids.Hom.has (@AlgebraicSpace.LocallySeparated S)
        (forget.{u + 1, u, u, u + 1} f) ↔
      Groupoids.Hom.has (@AlgebraicSpace.LocallySeparated S)
        (Hom.diagonal.{u + 1, u, u + 1} f) :=
  sorry

/-- The relative-inertia forgetful morphism is locally separated on scheme-slice
tests if and only if the identity section is an immersion. -/
theorem forget_locallySeparated_iff_identitySection_isImmersion
    {S : Scheme.{u}} {X Y : GroupoidsOver S} [AlgebraicStack X]
    [AlgebraicStack Y] (f : X ⟶ Y) :
    Groupoids.Hom.has (@AlgebraicSpace.LocallySeparated S)
        (forget.{u + 1, u, u, u + 1} f) ↔
      Groupoids.Hom.has (@AlgebraicSpace.IsImmersion S)
        (identitySection.{u + 1, u, u, u + 1} f) :=
  sorry

/-- The first diagonal of a morphism of algebraic stacks is locally separated
on scheme-slice tests if and only if the identity section is an immersion. -/
theorem firstDiagonal_locallySeparated_iff_identitySection_isImmersion
    {S : Scheme.{u}} {X Y : GroupoidsOver S} [AlgebraicStack X]
    [AlgebraicStack Y] (f : X ⟶ Y) :
    Groupoids.Hom.has (@AlgebraicSpace.LocallySeparated S)
        (Hom.diagonal.{u + 1, u, u + 1} f) ↔
      Groupoids.Hom.has (@AlgebraicSpace.IsImmersion S)
        (identitySection.{u + 1, u, u, u + 1} f) :=
  sorry

/-- Lemma 101.6.1 (4): Let `f : X ⟶ Y` be a morphism of algebraic stacks. The
following are equivalent: `I_{X/Y} ⟶ X` is unramified, and `f` is DM. -/
@[stacks 0CL0]
theorem forget_unramified_tfae {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) :
    List.TFAE
      [Groupoids.Hom.has (@AlgebraicSpace.Unramified S)
          (forget.{u + 1, u, u, u + 1} f),
        DM f] :=
  sorry

/-- The relative-inertia forgetful morphism is unramified on scheme-slice tests
if and only if `f` is DM. -/
theorem forget_unramified_iff_DM {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) :
    Groupoids.Hom.has (@AlgebraicSpace.Unramified S)
        (forget.{u + 1, u, u, u + 1} f) ↔
      DM f :=
  sorry

/-- Lemma 101.6.1 (5): Let `f : X ⟶ Y` be a morphism of algebraic stacks. The
following are equivalent: `I_{X/Y} ⟶ X` is locally quasi-finite, and `f` is
quasi-DM. -/
@[stacks 0CL0]
theorem forget_locallyQuasiFinite_tfae {S : Scheme.{u}}
    {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
    (f : X ⟶ Y) :
    List.TFAE
      [Groupoids.Hom.has (@AlgebraicSpace.LocallyQuasiFinite S)
          (forget.{u + 1, u, u, u + 1} f),
        QuasiDM f] :=
  sorry

/-- The relative-inertia forgetful morphism is locally quasi-finite on
scheme-slice tests if and only if `f` is quasi-DM. -/
theorem forget_locallyQuasiFinite_iff_quasiDM {S : Scheme.{u}}
    {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
    (f : X ⟶ Y) :
    Groupoids.Hom.has (@AlgebraicSpace.LocallyQuasiFinite S)
        (forget.{u + 1, u, u, u + 1} f) ↔
      QuasiDM f :=
  sorry

end AlgebraicGeometry.AlgebraicStack.RelativeInertia
