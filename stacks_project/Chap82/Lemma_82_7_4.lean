module

public import ReasLib.Topology.Specialization.Dimension
public import stacks_project.Chap65.Definition_65_13_2_Separation
public import stacks_project.Chap66.Lemma_66_12_3
public import stacks_project.Chap67.Definition_67_4_2_Separation
public import stacks_project.Chap68.Definition_68_25_4_UniversallyCatenary
public import stacks_project.Chap72.Definition_72_5_2
public import stacks_project.Chap76.Lemma_76_32_2_DimensionFunction

/-!
# Equal δ-dimension morphisms of good integral algebraic spaces

In Situation 82.2.1, a morphism of good integral algebraic spaces of equal
`δ`-dimension over `B` either factors through a proper closed subspace of the
target or is dominant with finite function-field extension.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Hom

/-- Lemma 82.7.4: In Situation 82.2.1 let `X, Y / B` be good and let
`f : X ⟶ Y` be a morphism over `B`. Assume `X`, `Y` integral and
`dim_δ(X) = dim_δ(Y)`, evaluated as equality of `pX.relativeDimensionFunction δ`
and `pY.relativeDimensionFunction δ` at generic points. Then either `f` factors
through a proper closed subspace of `Y`, or `f` is dominant and the extension of
function fields `R(X) / R(Y)` is finite. Here a proper closed subspace means a
`ClosedSubspace` whose point-set is not `Set.univ`, and `R(X)` is the residue
field at a generic point of `X`. -/
@[stacks 0ENY]
theorem factorsThrough_properClosed_or_finiteResidueFieldExtension
    {S : Scheme.{u}} {B X Y : AlgebraicSpace S}
    [UniversallyCatenary B] [IsQuasiSeparated B]
    (pX : X ⟶ B) (pY : Y ⟶ B)
    [QuasiSeparated pX] [LocallyOfFiniteType pX]
    [QuasiSeparated pY] [LocallyOfFiniteType pY]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ Y) (hf : f ≫ pY = pX)
    {x : Points X} {y : Points Y}
    (hx : x ∈ genericPoints X) (hy : y ∈ genericPoints Y)
    (hdim : pX.relativeDimensionFunction δ x = pY.relativeDimensionFunction δ y) :
    (∃ Z : ClosedSubspace Y,
        Z.pointsSet ≠ Set.univ ∧ ∃ g : X ⟶ Z.X, g ≫ Z.ι = f) ∨
      (Dominant f ∧ FiniteResidueFieldExtensionAt f x) :=
  sorry

/-- If in addition `f` is dominant and the generic relative dimensions agree,
then `FiniteResidueFieldExtension f` holds. Here `dim_δ(X)` is
`pX.relativeDimensionFunction δ` at a generic point and `R(X)` is the residue
field at that point. -/
theorem finiteResidueFieldExtension_of_eq_deltaDimension
    {S : Scheme.{u}} {B X Y : AlgebraicSpace S}
    [UniversallyCatenary B] [IsQuasiSeparated B]
    (pX : X ⟶ B) (pY : Y ⟶ B)
    [QuasiSeparated pX] [LocallyOfFiniteType pX]
    [QuasiSeparated pY] [LocallyOfFiniteType pY]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ Y) (hf : f ≫ pY = pX) [Dominant f]
    {x : Points X} {y : Points Y}
    (hx : x ∈ genericPoints X) (hy : y ∈ genericPoints Y)
    (hdim : pX.relativeDimensionFunction δ x = pY.relativeDimensionFunction δ y) :
    FiniteResidueFieldExtension f :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Hom
