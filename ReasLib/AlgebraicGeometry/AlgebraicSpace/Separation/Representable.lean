module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated

/-!
# Separation properties of representable morphisms of algebraic spaces

For representable morphisms, diagonal separation conditions agree with the
corresponding conditions on scheme base changes. On morphisms induced by schemes,
they agree with the ordinary scheme separation conditions.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits MorphismProperty

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Every representable morphism of algebraic spaces is locally separated. -/
theorem locallySeparated_of_relativelyRepresentable
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    (hf : yoneda.relativelyRepresentable f) : LocallySeparated f :=
  sorry

/-- For a representable morphism of algebraic spaces, separatedness on scheme
base changes is equivalent to the relative diagonal being a closed immersion. -/
theorem separated_presheaf_iff_separated
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    (hf : yoneda.relativelyRepresentable f) :
    (over (@AlgebraicGeometry.IsSeparated : MorphismProperty Scheme.{u})).presheaf f ↔
      Separated f :=
  sorry

/-- For a representable morphism of algebraic spaces, quasi-separatedness on scheme
base changes is equivalent to the relative diagonal being quasi-compact. -/
theorem quasiSeparated_presheaf_iff_quasiSeparated
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    (hf : yoneda.relativelyRepresentable f) :
    (over (@AlgebraicGeometry.QuasiSeparated : MorphismProperty Scheme.{u})).presheaf f ↔
      QuasiSeparated f :=
  sorry

/-- A scheme morphism over the base induces a separated morphism of algebraic spaces
if and only if the underlying scheme morphism is separated. -/
theorem separated_ofOverMap_iff {S : Scheme.{u}} {U V : Over S} (h : U ⟶ V) :
    Separated (ofOverMap h) ↔ AlgebraicGeometry.IsSeparated h.left :=
  sorry

/-- A scheme morphism over the base induces a quasi-separated morphism of algebraic spaces
if and only if the underlying scheme morphism is quasi-separated. -/
theorem quasiSeparated_ofOverMap_iff {S : Scheme.{u}} {U V : Over S}
    (h : U ⟶ V) :
    QuasiSeparated (ofOverMap h) ↔ AlgebraicGeometry.QuasiSeparated h.left :=
  sorry

/-- Every morphism of algebraic spaces induced by a scheme morphism over the base is
locally separated. -/
instance locallySeparated_ofOverMap {S : Scheme.{u}} {U V : Over S} (h : U ⟶ V) :
    LocallySeparated (ofOverMap h) :=
  locallySeparated_of_relativelyRepresentable (Functor.relativelyRepresentable.map yoneda h)

/-- A separated scheme morphism over the base induces a separated morphism of algebraic spaces. -/
instance instSeparated_ofOverMap {S : Scheme.{u}} {U V : Over S} (h : U ⟶ V)
    [AlgebraicGeometry.IsSeparated h.left] : Separated (ofOverMap h) :=
  (separated_ofOverMap_iff h).mpr inferInstance

/-- Quasi-separatedness of the induced morphism of algebraic spaces implies
quasi-separatedness of its representing scheme morphism. -/
instance instQuasiSeparated_left_ofOverMap {S : Scheme.{u}} {X0 Y0 : Over S}
    (f0 : X0 ⟶ Y0) [QuasiSeparated (ofOverMap f0)] :
    AlgebraicGeometry.QuasiSeparated f0.left :=
  (quasiSeparated_ofOverMap_iff f0).mp inferInstance

end AlgebraicGeometry.AlgebraicSpace
