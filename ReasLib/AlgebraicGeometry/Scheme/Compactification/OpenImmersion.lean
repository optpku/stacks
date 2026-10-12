/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Compactification.FixedInterior
public import ReasLib.AlgebraicGeometry.Scheme.FiniteTypeSeparatedOver

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Compactification.Of

/-- The map underlying an open immersion over `S` is also a map to the identity object over
its target. -/
theorem openImmersion_over {S : Scheme.{u}} [IsNoetherian S]
    {X Y : Scheme.FiniteTypeSeparatedOver S} (j : X ⟶ Y) :
    j.hom.left ≫ 𝟙 Y.obj.left = j.hom.left := sorry

/-- The morphism to the identity object used by the canonical compactification is an open
immersion. -/
theorem openImmersionHom_isOpenImmersion {S : Scheme.{u}} [IsNoetherian S]
    {X Y : Scheme.FiniteTypeSeparatedOver S} (j : X ⟶ Y)
    [IsOpenImmersion j.hom.left] :
    IsOpenImmersion
      (Over.homMk j.hom.left (openImmersion_over j) :
        Over.mk j.hom.left ⟶ Over.mk (𝟙 Y.obj.left)).left := sorry

/-- The morphism to the identity object used by the canonical compactification is
quasi-compact. -/
theorem openImmersionHom_quasiCompact {S : Scheme.{u}} [IsNoetherian S]
    {X Y : Scheme.FiniteTypeSeparatedOver S} (j : X ⟶ Y)
    [IsOpenImmersion j.hom.left] :
    QuasiCompact
      (Over.homMk j.hom.left (openImmersion_over j) :
        Over.mk j.hom.left ⟶ Over.mk (𝟙 Y.obj.left)).left := sorry

/-- The identity object over the target is proper over the target. -/
theorem openImmersionAmbient_isProper {S : Scheme.{u}} [IsNoetherian S]
    {Y : Scheme.FiniteTypeSeparatedOver S} :
    IsProper (Over.mk (𝟙 Y.obj.left)).hom := sorry

/-- The canonical compactification of an open immersion uses its target as ambient scheme. -/
@[reducible]
def openImmersion {S : Scheme.{u}} [IsNoetherian S]
    {X Y : Scheme.FiniteTypeSeparatedOver S} (j : X ⟶ Y)
    [IsOpenImmersion j.hom.left] : Of Y.obj.left (Over.mk j.hom.left) :=
  @mk Y.obj.left _ (Over.mk (𝟙 Y.obj.left))
    (Over.homMk j.hom.left (openImmersion_over j) :
      Over.mk j.hom.left ⟶ Over.mk (𝟙 Y.obj.left))
    (openImmersionHom_isOpenImmersion j) (openImmersionHom_quasiCompact j)
    openImmersionAmbient_isProper

/-- The interior map of the canonical compactification of an open immersion is the given map. -/
theorem openImmersion_ι {S : Scheme.{u}} [IsNoetherian S]
    {X Y : Scheme.FiniteTypeSeparatedOver S} (j : X ⟶ Y)
    [IsOpenImmersion j.hom.left] : ι (openImmersion j) = j.hom.left := sorry

end AlgebraicGeometry.Scheme.Compactification.Of
