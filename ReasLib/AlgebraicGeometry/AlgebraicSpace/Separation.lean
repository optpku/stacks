/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Diagonal
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.CategoryTheory.Limits.Types.Colimits
public import Mathlib.CategoryTheory.Limits.Types.Limits
public import Mathlib.CategoryTheory.MorphismProperty.Comma
public import Mathlib.CategoryTheory.MorphismProperty.Representable
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism
public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.Separation

/-!
# Separation conditions on algebraic spaces and their morphisms

An algebraic space or a morphism of algebraic spaces is separated, locally separated,
or quasi-separated according as its diagonal is a representable closed immersion,
a representable immersion, or a representable quasi-compact morphism. Zariski-local
quasi-separatedness is expressed by a covering by quasi-separated open subspaces.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits MorphismProperty

noncomputable section

universe u w

namespace AlgebraicGeometry.AlgebraicSpace

/-- The diagonal morphism of an algebraic space, as the binary product diagonal of its functor of
points. -/
abbrev diag {S : Scheme.{u}} (F : AlgebraicSpace S) :
    F.functorOfPoints ⟶ F.functorOfPoints ⨯ F.functorOfPoints :=
  Limits.diag F.functorOfPoints

/-- The diagonal of an algebraic space is the product diagonal of its functor of points. -/
theorem diag_def {S : Scheme.{u}} (F : AlgebraicSpace S) :
    diag F = Limits.diag F.functorOfPoints :=
  rfl

/-- A family of morphisms `ι i : Fi i ⟶ F` is a Zariski covering if each `ι i` is a representable
open immersion and the coproduct of the source functors is locally surjective onto `F` as fppf
sheaves. -/
def IsZariskiCover {S : Scheme.{u}} {I : Type w} [Small.{u} I] (F : AlgebraicSpace S)
    (Fi : I → AlgebraicSpace S) (ι : ∀ i, Fi i ⟶ F) : Prop :=
  (∀ i, (MorphismProperty.over (@IsOpenImmersion)).presheaf (ι i)) ∧
    Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S)
      (Sigma.desc fun i ↦ (ι i : (Fi i).functorOfPoints ⟶ F.functorOfPoints))

/-- A Zariski covering consists of representable open immersions whose coproduct is locally
surjective as fppf sheaves. -/
theorem isZariskiCover_spec {S : Scheme.{u}} {I : Type w} [Small.{u} I] {F : AlgebraicSpace S}
    {Fi : I → AlgebraicSpace S} {ι : ∀ i, Fi i ⟶ F} :
    IsZariskiCover F Fi ι ↔
      (∀ i, (MorphismProperty.over (@IsOpenImmersion)).presheaf (ι i)) ∧
        Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S)
          (Sigma.desc fun i ↦ (ι i : (Fi i).functorOfPoints ⟶ F.functorOfPoints)) :=
  sorry

/-- The identity family on an algebraic space is a Zariski covering. -/
theorem isZariskiCover_id {S : Scheme.{u}} (F : AlgebraicSpace S) :
    IsZariskiCover F (fun _ : PUnit.{u + 1} ↦ F) (fun _ : PUnit.{u + 1} ↦ 𝟙 F) :=
  sorry

/-- An algebraic space is separated over its base if the diagonal is a closed immersion. -/
@[mk_iff]
class IsSeparated {S : Scheme.{u}} (F : AlgebraicSpace S) : Prop where
  /-- The diagonal is a representable closed immersion. -/
  isClosedImmersion_diagonal : (MorphismProperty.over (@IsClosedImmersion)).presheaf (diag F)

/-- An algebraic space is locally separated over its base if the diagonal is an immersion. This
does not include quasi-separatedness. -/
@[mk_iff]
class IsLocallySeparated {S : Scheme.{u}} (F : AlgebraicSpace S) : Prop where
  /-- The diagonal is a representable immersion. -/
  isImmersion_diagonal : (MorphismProperty.over (@IsImmersion)).presheaf (diag F)

/-- An algebraic space is quasi-separated over its base if the diagonal is quasi-compact. -/
@[mk_iff]
class IsQuasiSeparated {S : Scheme.{u}} (F : AlgebraicSpace S) : Prop where
  /-- The diagonal is a representable quasi-compact morphism. -/
  quasiCompact_diagonal : (MorphismProperty.over (@QuasiCompact)).presheaf (diag F)

/-- An algebraic space is Zariski locally quasi-separated over its base if it admits a Zariski
covering by quasi-separated open subspaces. -/
@[mk_iff]
class IsZariskiLocallyQuasiSeparated {S : Scheme.{u}} (F : AlgebraicSpace S) : Prop where
  /-- There is a Zariski covering by quasi-separated algebraic spaces. -/
  exists_zariskiCover : ∃ (I : Type u) (_ : Small.{u} I) (Fi : I → AlgebraicSpace S)
    (ι : ∀ i, Fi i ⟶ F), IsZariskiCover F Fi ι ∧ ∀ i, IsQuasiSeparated (Fi i)

/-- The algebraic space represented by a separated scheme over its base is separated. -/
instance instIsSeparated_ofOver {S : Scheme.{u}} (T : CategoryTheory.Over S)
    [AlgebraicGeometry.IsSeparated T.hom] : IsSeparated (ofOver T) := sorry

/-- A separated algebraic space is locally separated. -/
instance (priority := 900) instIsLocallySeparated {S : Scheme.{u}} (F : AlgebraicSpace S)
    [IsSeparated F] : IsLocallySeparated F :=
  sorry

/-- A separated algebraic space is quasi-separated. -/
instance (priority := 900) instIsQuasiSeparated {S : Scheme.{u}} (F : AlgebraicSpace S)
    [IsSeparated F] : IsQuasiSeparated F :=
  sorry

/-- A quasi-separated algebraic space is Zariski locally quasi-separated, via the singleton
covering. -/
instance (priority := 900) instIsZariskiLocallyQuasiSeparated {S : Scheme.{u}}
    (F : AlgebraicSpace S) [IsQuasiSeparated F] : IsZariskiLocallyQuasiSeparated F := sorry

/-- Separatedness of an algebraic-space morphism is the corresponding
separatedness predicate on its functor-of-points transformation. -/
abbrev Separated {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) : Prop :=
  FormalAlgebraicSpace.Separated (f : X.functorOfPoints ⟶ Y.functorOfPoints)

/-- A morphism of algebraic spaces is locally separated if the relative diagonal is an immersion.
This does not include quasi-separatedness. -/
@[mk_iff]
class LocallySeparated {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) : Prop where
  /-- The relative diagonal is a representable immersion. -/
  isImmersion_diagonal :
    (over (@AlgebraicGeometry.IsImmersion : MorphismProperty Scheme.{u})).presheaf
      (pullback.diagonal (C := (Over S)ᵒᵖ ⥤ Type u) f)

/-- Quasi-separatedness is the corresponding predicate on functorial points. -/
abbrev QuasiSeparated {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) : Prop :=
  FormalAlgebraicSpace.QuasiSeparated (f : X.functorOfPoints ⟶ Y.functorOfPoints)

namespace Separated

/-- The identity morphism of an algebraic space is separated. -/
instance id {S : Scheme.{u}} {X : AlgebraicSpace S} : Separated (𝟙 X) := sorry

/-- An isomorphism of algebraic spaces is separated. -/
instance of_isIso {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [IsIso f] :
    Separated f := sorry

/-- A monomorphism of algebraic spaces is separated. -/
instance of_mono {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [Mono f] : Separated f := sorry

/-- A morphism of algebraic spaces is separated if and only if the relative diagonal is a
representable closed immersion. -/
theorem spec {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    Separated f ↔
      (over (@AlgebraicGeometry.IsClosedImmersion : MorphismProperty Scheme.{u})).presheaf
        (pullback.diagonal (C := (Over S)ᵒᵖ ⥤ Type u) f) :=
  sorry

end Separated

namespace LocallySeparated

/-- The identity morphism of an algebraic space is locally separated. -/
instance id {S : Scheme.{u}} {X : AlgebraicSpace S} : LocallySeparated (𝟙 X) := sorry

/-- An isomorphism of algebraic spaces is locally separated. -/
instance of_isIso {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [IsIso f] :
    LocallySeparated f := sorry

/-- A separated morphism of algebraic spaces is locally separated. -/
@[instance 900]
theorem of_separated {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [Separated f] : LocallySeparated f := sorry

/-- A morphism of algebraic spaces is locally separated if and only if the relative diagonal is a
representable immersion. -/
theorem spec {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    LocallySeparated f ↔
      (over (@AlgebraicGeometry.IsImmersion : MorphismProperty Scheme.{u})).presheaf
        (pullback.diagonal (C := (Over S)ᵒᵖ ⥤ Type u) f) :=
  sorry

end LocallySeparated

namespace QuasiSeparated

/-- The identity morphism of an algebraic space is quasi-separated. -/
instance id {S : Scheme.{u}} {X : AlgebraicSpace S} : QuasiSeparated (𝟙 X) := sorry

/-- An isomorphism of algebraic spaces is quasi-separated. -/
instance of_isIso {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [IsIso f] :
    QuasiSeparated f := sorry

/-- A separated morphism of algebraic spaces is quasi-separated. -/
@[instance 900]
theorem of_separated {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [Separated f] : QuasiSeparated f := sorry

/-- A morphism of algebraic spaces is quasi-separated if and only if the relative diagonal is a
representable quasi-compact morphism. -/
theorem spec {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    QuasiSeparated f ↔
      (over (@AlgebraicGeometry.QuasiCompact : MorphismProperty Scheme.{u})).presheaf
        (pullback.diagonal (C := (Over S)ᵒᵖ ⥤ Type u) f) :=
  sorry

end QuasiSeparated

end AlgebraicGeometry.AlgebraicSpace
