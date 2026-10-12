/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap65.Lemma_65_12_4_Immersion
public import stacks_project.Chap67.Definition_67_21_2_QuasiAffine
public import stacks_project.Chap67.Remark_67_20_9_Factorization

/-!
# Quasi-affine morphisms via relative spectrum factorization

A qcqs morphism of algebraic spaces is quasi-affine iff the canonical first factor
through the relative spectrum of the pushforward structure sheaf is an open
immersion.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace QuasiAffine

/-- A qcqs morphism of algebraic spaces is quasi-affine iff the canonical morphism
to the relative spectrum of the pushforward structure sheaf is an open immersion. -/
theorem iff_isOpenImmersion_toPushforwardRelativeSpec {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f] :
    QuasiAffine f ↔ IsOpenImmersion (Hom.toPushforwardRelativeSpec f) :=
  sorry

/-- A qcqs morphism of algebraic spaces whose canonical morphism to the relative
spectrum of the pushforward structure sheaf is an open immersion is quasi-affine. -/
theorem of_isOpenImmersion_toPushforwardRelativeSpec {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    [IsOpenImmersion (Hom.toPushforwardRelativeSpec f)] : QuasiAffine f :=
  sorry

end QuasiAffine

/-- The canonical morphism of a qcqs quasi-affine morphism of algebraic spaces into
the relative spectrum of the pushforward structure sheaf is an open immersion. -/
instance instIsOpenImmersion_toPushforwardRelativeSpec {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    [QuasiAffine f] : IsOpenImmersion (Hom.toPushforwardRelativeSpec f) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
